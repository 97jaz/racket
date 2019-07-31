(define-record-type hamt-node
  [fields (immutable count)
          (immutable data)]
  [nongenerative #{hamt-node kt3t3eb6ndw7a3l7l1wtmuxsh-0}])

(define-record-type hamt-bitmap-node
  [parent hamt-node]
  [fields (immutable bitmap)]
  [nongenerative #{hamt-node kt3t3eb6ndw7a3l7l1wtmuxsh-1}]
  [sealed #t])

(define-record-type hamt-collision-node
  [parent hamt-node]
  [fields (immutable hash)]
  [nongenerative #{hamt-node kt3t3eb6ndw7a3l7l1wtmuxsh-2}]
  [sealed #t])

(define empty-hamt-node
  (make-hamt-bitmap-node 0 (vector) 0))

(define bit-partition-width 4)
(define bit-partition-mask #b1111)
;;(define bit-partition-width 5)
;;(define bit-partition-mask #b11111)
(define hash-code-length (fxbit-count (most-positive-fixnum)))

(define (downshift shift)
  (fx+ bit-partition-width shift))

(define (hamt-node-ref node hash key extract default eqtype shift)
  (cond
   [(hamt-bitmap-node? node)
    (hamt-bitmap-node-ref node hash key extract default eqtype shift)]
   [else
    (hamt-collision-node-ref node key extract default eqtype)]))

(define (hamt-bitmap-node-ref node hash key extract default eqtype shift)
  (let loop ([node node] [shift shift])
    (let ([bitmap (hamt-bitmap-node-bitmap node)]
          [bit (hash+shift->bit hash shift)])
      (cond
       [(bitmap-has-bit? bitmap bit)
        (let* ([idx (bitmap+bit->index bitmap bit)]
               [item (#%vector-ref (hamt-node-data node) idx)])
          (cond
           [(hamt-bitmap-node? item)
            (loop item (downshift shift))]
           [(pair? item)
            (if (key=? eqtype key (car item))
                (extract item)
                default)]
           [(fx= hash (hamt-collision-node-hash item))
            (hamt-collision-node-ref item key extract default eqtype)]
           [else
            default]))]
       [else
        default]))))

(define (hamt-collision-node-ref node key extract default eqtype)
  (let ([idx (hamt-collision-node-index node key eqtype)])
    (if idx
        (extract (#%vector-ref (hamt-node-data node) idx))
        default)))

(define (hamt-bitmap-node-set node hash key val eqtype)
  (let loop ([node node] [shift 0])
    (let ([bitmap (hamt-bitmap-node-bitmap node)]
          [bit (hash+shift->bit hash shift)])
      (cond
       [(bitmap-has-bit? bitmap bit)
        (let* ([idx (bitmap+bit->index bitmap bit)]
               [item (#%vector-ref (hamt-node-data node) idx)])
          (cond
           [(hamt-bitmap-node? item)
            (hamt-bitmap-node-replace-child node idx item (loop item (downshift shift)))]
           [(pair? item)
            (cond
             [(key=? eqtype key (car item))
              (hamt-bitmap-node-replace-pair node idx (cons key val) 0)]
             [else
              (let* ([old-hash (compute-hash eqtype (car item))]
                     [new-child (hamt-node-merge item old-hash (cons key val) hash eqtype (downshift shift))])
                (hamt-bitmap-node-replace-pair node idx new-child 1))])]
           [else
            (let ([new-child (hamt-collision-node-set item key val eqtype)])
              (hamt-bitmap-node-replace-child node idx item new-child))]))]
       [else
        (make-hamt-bitmap-node
         (fx+ 1 (hamt-node-count node))
         (vector-insert (hamt-node-data node)
                        (bitmap+bit->index bitmap bit)
                        (cons key val))
         (fxior bitmap bit))]))))

(define (hamt-node-merge old-pair old-hash new-pair new-hash eqtype shift)
  (cond
   [(fx>= shift hash-code-length)
    (make-hamt-collision-node 2 (vector old-pair new-pair) old-hash)]
   [else
    (let ([old-mask (hash+shift->mask old-hash shift)]
          [new-mask (hash+shift->mask new-hash shift)])
      (cond
       [(fx= old-mask new-mask)
        (let ([child (hamt-node-merge old-pair old-hash new-pair new-hash eqtype (downshift shift))])
          (make-hamt-bitmap-node (hamt-node-count child) (vector child) (mask->bit old-mask)))]
       [else
        (let ([bitmap (fxior (mask->bit old-mask) (mask->bit new-mask))])
          (if (fx< old-mask new-mask)
              (make-hamt-bitmap-node 2 (vector old-pair new-pair) bitmap)
              (make-hamt-bitmap-node 2 (vector new-pair old-pair) bitmap)))]))]))

(define (hamt-bitmap-node-replace-pair node idx new-child count-diff)
  (make-hamt-bitmap-node
   (fx+ (hamt-node-count node) count-diff)
   (vector-replace (hamt-node-data node) idx new-child)
   (hamt-bitmap-node-bitmap node)))

(define (hamt-bitmap-node-replace-child node idx old-child new-child)
  (make-hamt-bitmap-node
   (fx+ (hamt-node-count node)
        (fx- (hamt-node-count new-child)
             (hamt-node-count old-child)))
   (vector-replace (hamt-node-data node) idx new-child)
   (hamt-bitmap-node-bitmap node)))

(define (hamt-collision-node-set node key val eqtype)
  (let ([idx (hamt-collision-node-index node key eqtype)])
    (if idx
        (make-hamt-collision-node
         (hamt-node-count node)
         (vector-replace (hamt-node-data node) idx (cons key val))
         (hamt-collision-node-hash node))
        (make-hamt-collision-node
         (fx+ 1 (hamt-node-count node))
         (vector-append (hamt-node-data node) (cons key val))
         (hamt-collision-node-hash node)))))

(define (hamt-bitmap-node-remove node hash key eqtype)
  (let loop ([node node] [shift 0])
    (let ([bitmap (hamt-bitmap-node-bitmap node)]
          [bit (hash+shift->bit hash shift)])
      (cond
       [(bitmap-has-bit? bitmap bit)
        (let* ([idx (bitmap+bit->index bitmap bit)]
               [item (#%vector-ref (hamt-node-data node) idx)])
          (cond
           [(hamt-bitmap-node? item)
            (let ([new-child (loop item (downshift shift))])
              (hamt-bitmap-node-remove/singleton node item new-child idx bit))]
           [(pair? item)
            (cond
             [(key=? eqtype key (car item))
              (cond
               [(and (fx= 2 (hamt-node-count node))
                     (fx= 2 (hamt-popcount bitmap)))
                (make-hamt-bitmap-singleton node hash idx bit shift)]
               [else
                (make-hamt-bitmap-node (fx- (hamt-node-count node) 1)
                                       (vector-remove (hamt-node-data node) idx)
                                       (fxxor bitmap bit))])]
             [else
              node])]
           [else
            (let ([new-child (hamt-collision-node-remove item hash key eqtype)])
              (hamt-bitmap-node-remove/singleton node item new-child idx bit))]))]
       [else
        node]))))

(define (hamt-bitmap-node-remove/singleton node item new-child idx bit)
  (cond
   [(fx= 1 (hamt-node-count new-child))
    (cond
     [(fx= (hamt-bitmap-node-bitmap node) bit)
      new-child]
     [else
      (let ([pair (#%vector-ref (hamt-node-data new-child) 0)])
        (hamt-bitmap-node-replace-pair node idx pair -1))])]
   [else
    (hamt-bitmap-node-replace-child node idx item new-child)]))

(define (make-hamt-bitmap-singleton node hash idx bit shift)
  ;; After we remove the pair at idx, we'll be left with a singleton,
  ;; which will either become the new root, or else it will be unwrapped,
  ;; and its remaining pair will be inlined in another node.
  (let ([new-bitmap (if (fx= 0 shift)
                        (fxxor (hamt-bitmap-node-bitmap node) bit)
                        (hash+shift->bit hash 0))]
        [other-idx (if (fx= 0 idx) 1 0)])
    (let ([pair (#%vector-ref (hamt-node-data node) other-idx)])
      (make-hamt-bitmap-node 1 (vector pair) new-bitmap))))

(define (hamt-collision-node-remove node hash key eqtype)
  (cond
   [(fx= hash (hamt-collision-node-hash node))
    (let ([idx (hamt-collision-node-index node key eqtype)])
      (if idx
          (make-hamt-collision-node (fx- (hamt-node-count node) 1)
                                    (vector-remove (hamt-node-data node) idx)
                                    hash)
          node))]
   [else
    node]))

(define (hamt-collision-node-index node key eqtype)
  (let ([data (hamt-node-data node)])
    (let loop ([i (#%vector-length data)])
      (cond
       [(fx> i 0)
        (let ([pair (#%vector-ref data (fx- i 1))])
          (if (key=? eqtype key (car pair))
              i
              (loop (fx- i 1))))]
       [else
        #f]))))

(define (hamt-node-nth node n)
  (let* ([data (hamt-node-data node)]
         [len (#%vector-length data)])
    (let loop ([i 0] [n n])
      (cond
       [(fx< i len)
        (let ([item (#%vector-ref data i)])
          (cond
           [(hamt-node? item)
            (let ([count (hamt-node-count item)])
              (if (fx< n count)
                  (hamt-node-nth item n)
                  (loop (fx+ 1 i) (fx- n count))))]
           [(fx= 0 n)
            item]
           [else
            (loop (fx+ 1 i) (fx- n 1))]))]
       [else
        #f]))))

(define (hamt-iterate-first h)
  (and (fx> (hamt-count h) 0)
       0))

(define (hamt-iterate-next h pos)
  (let ([pos (fx+ 1 pos)])
    (and (not (fx= pos (hamt-count h)))
         pos)))

(define-syntax-rule (hamt-iterate-pair* h pos extract fail)
  (let ([pair (hamt-node-nth (hamt-root h) pos)])
    (if pair
        (extract pair)
        fail)))

(define (hamt-iterate-pair h pos fail)
  (hamt-iterate-pair* h pos (lambda (x) x) fail))

(define (hamt-iterate-key h pos fail)
  (hamt-iterate-pair* h pos car fail))

(define (hamt-iterate-value h pos fail)
  (hamt-iterate-pair* h pos cdr fail))

(define (hamt-iterate-key+value h pos fail)
  (hamt-iterate-pair* h
                      pos
                      (lambda (pair)
                        (values (car pair) (cdr pair)))
                      fail))

(define (hamt-node-enum pos stack)
  (let ([node (car pos)]
        [i (cdr pos)])
    (let ([data (hamt-node-data node)])
      (cond
       [(fx< i (#%vector-length data))
        (let ([item (#%vector-ref data i)]
              [stack (cons (cons node (fx+ 1 i)) stack)])
          (cond
           [(hamt-node? item)
            (hamt-node-enum (cons item 0) stack)]
           [else
            (cons item stack)]))]
       [(null? stack)
        #f]
       [else
        (hamt-node-enum (car stack) (cdr stack))]))))

(define (unsafe-hamt-node-iterate-first node)
  (and (fx> (hamt-node-count node) 0)
       (hamt-node-enum (cons node 0) '())))

(define (unsafe-hamt-iterate-first h)
  (unsafe-hamt-node-iterate-first (hamt-root h)))

(define (unsafe-hamt-node-iterate-next pos)
  (let ([next (cdr pos)])
    (hamt-node-enum (car next) (cdr next))))

(define (unsafe-hamt-iterate-next h pos)
  (unsafe-hamt-node-iterate-next pos))

(define (unsafe-hamt-iterate-pair h pos)
  (car pos))

(define (unsafe-hamt-iterate-key h pos)
  (caar pos))

(define (unsafe-hamt-iterate-value h pos)
  (cdar pos))

(define (unsafe-hamt-iterate-key+value h pos)
  (values (caar pos) (cdar pos)))

(define (hamt-node=? a b eqtype val=?)
  (and
   (fx= (hamt-node-count a)
        (hamt-node-count b))

   (let ([data-a (hamt-node-data a)]
         [data-b (hamt-node-data b)])
     (cond
      [(hamt-bitmap-node? a)
       (and (hamt-bitmap-node? b)
            (fx= (hamt-bitmap-node-bitmap a)
                 (hamt-bitmap-node-bitmap b))
            (let loop ([i (#%vector-length data-a)])
              (cond
               [(fx> i 0)
                (let ([item-a (#%vector-ref data-a (fx- i 1))]
                      [item-b (#%vector-ref data-b (fx- i 1))])
                  (cond
                   [(and (hamt-node? item-a)
                         (hamt-node? item-b))
                    (and (hamt-node=? item-a item-b eqtype val=?)
                         (loop (fx- i 1)))]
                   [(and (pair? item-a)
                         (pair? item-b))
                    (and (key=? eqtype (car item-a) (car item-b))
                         (val=? (cdr item-a) (cdr item-b))
                         (loop (fx- i 1)))]
                   [else
                    #f]))]
               [else
                #t])))]
      [else
       (and (hamt-collision-node? b)
            (let loop ([i (#%vector-length data-a)])
              (cond
               [(fx> i 0)
                (let* ([pair-a (#%vector-ref data-a (fx- i 1))]
                       [pair-b (hamt-collision-node-ref b (car pair-a) (lambda (x) x) #f eqtype)])
                  (and pair-b
                       (val=? (cdr pair-a)
                              (cdr pair-b))
                       (loop (fx- i 1))))]
               [else
                #t])))]))))

(define (hamt-node-keys-subset?/bitmap-to-bitmap a b eqtype shift)
  (let ([data-a (hamt-node-data a)]
        [data-b (hamt-node-data b)]
        [bitmap-a (hamt-bitmap-node-bitmap a)]
        [bitmap-b (hamt-bitmap-node-bitmap b)])
  (and
   (fx= bitmap-a (fxand bitmap-a bitmap-b))

   (let loop ([ai 0] [bi 0] [bit 0])
     (cond
      [(fx= ai (#%vector-length data-a))
       #t]
      [(fxbit-set? bitmap-a bit)
       (let ([item-a (#%vector-ref data-a ai)]
             [item-b (#%vector-ref data-b bi)])
         (and
          (cond
           [(pair? item-a)
            (cond
             [(pair? item-b)
              (key=? eqtype (car item-a) (car item-b))]
             [(hamt-bitmap-node? item-b)
              (let* ([key (car item-a)]
                     [hash (compute-hash eqtype key)])
                (hamt-bitmap-node-ref item-b hash key (lambda (_) #t) #f eqtype (downshift shift)))]
             [else
              (hamt-collision-node-ref item-b (car item-a) (lambda (_) #t) #f eqtype)])]
           [(pair? item-b)
            #f]
           [else
            (hamt-node-keys-subset? item-a item-b eqtype (downshift shift))])
          (loop (fx+ 1 ai) (fx+ 1 bi) (fx+ 1 bit))))]
      [(fxbit-set? bitmap-b bit)
       (loop ai (fx+ 1 bi) (fx+ 1 bit))]
      [else
       (loop ai bi (fx+ 1 bit))])))))

(define (hamt-node-keys-subset? a b eqtype shift)
  (or
   (eq? a b)
   (and
    (fx<= (hamt-node-count a)
          (hamt-node-count b))

    (cond
     [(and (hamt-bitmap-node? a)
           (hamt-bitmap-node? b))
      (hamt-node-keys-subset?/bitmap-to-bitmap a b eqtype shift)]
     [else
      (let loop ([pos (unsafe-hamt-node-iterate-first a)])
        (cond
         [pos
          (let* ([key (unsafe-hamt-iterate-key pos)]
                 [hash (compute-hash eqtype key)])
            (and
             (hamt-node-ref b hash key (lambda (_) #t) #f eqtype shift)
             (loop (unsafe-hamt-node-iterate-next pos))))]
         [else
          #t]))]))))

(define (hamt-node-hash-code node compute-hash hash)
  (cond
   [(hamt-bitmap-node? node)
    (let* ([data (hamt-node-data node)]
           [len (#%vector-length data)])
      (let loop ([i 0] [hash (hash-code-combine hash (hamt-bitmap-node-bitmap node))])
        (cond
         [(fx= i len)
          hash]
         [else
          (let ([item (#%vector-ref data i)])
            (cond
             [(pair? item)
              (loop (fx+ 1 i) (hash-code-combine hash (compute-hash (cdr item))))]
             [else
              (loop (fx+ 1 i) (hamt-node-hash-code item compute-hash hash))]))])))]
   [else
    (hash-code-combine hash (hamt-collision-node-hash node))]))

(define (hash+shift->bit hash shift)
  (mask->bit (hash+shift->mask hash shift)))

(define (hash+shift->mask hash shift)
  (fxand (fxsrl hash shift) bit-partition-mask))

(define (mask->bit mask)
  (fxsll 1 mask))

(define (bitmap-has-bit? bitmap bit)
  (not (fx= 0 (fxand bit bitmap))))

(define (bitmap+bit->index bitmap bit)
  (hamt-popcount (fxand bitmap (fx- bit 1))))

(define (key=? eqtype k1 k2)
  (cond
   [(eq? eqtype 'eq)    (eq? k1 k2)]
   [(eq? eqtype 'equal) (key-equal? k1 k2)]
   [else                (eqv? k1 k2)]))

(define (compute-hash eqtype k)
  (cond
   [(eq? eqtype 'eq)    (eq-hash-code k)]
   [(eq? eqtype 'equal) (key-equal-hash-code k)]
   [else                (eqv-hash-code k)]))

(define (popcount16 x)
  (let* ([x (fx- x (fxand (fxsrl x 1) #x5555))]
         [x (fx+ (fxand x #x3333) (fxand (fxsrl x 2) #x3333))]
         [x (fxand (fx+ x (fxsrl x 4)) #x0f0f)]
         [x (fx+ x (fxsrl x 8))])
    (fxand x #x1f)))

(define popcount32
  (let ([tbl (#%make-vector (expt 2 16))])
    (let loop ([i 0])
      (when (fx< i (#%vector-length tbl))
        (#%vector-set-fixnum! tbl i (fxbit-count i))
        (loop (fx+ 1 i))))
    (lambda (x)
      (fx+ (#%vector-ref tbl (fxand x #xffff))
           (#%vector-ref tbl (fxsrl x 16))))))

(define hamt-popcount popcount16)

(define (hamt-vector-set! vec idx child)
  (#%vector-set! vec idx child))

(define (hamt-vector-copy! dst dst-start src src-start src-end)
  (let loop ([i (fx- src-end src-start 1)])
    (cond
     [(fx> i 0)
      (hamt-vector-set! dst (fx+ i dst-start) (#%vector-ref src (fx+ i src-start)))
      (let ([i (fx- i 1)])
        (hamt-vector-set! dst (fx+ i dst-start) (#%vector-ref src (fx+ i src-start))))
      (loop (fx- i 2))]
     [(fx= 0 i)
      (hamt-vector-set! dst (fx+ i dst-start) (#%vector-ref src (fx+ i src-start)))])))

(define (vector-replace vec idx child)
  (let ([new-vec (#%vector-copy vec)])
    (hamt-vector-set! new-vec idx child)
    new-vec))

(define (vector-insert vec idx child)
  (let* ([len (#%vector-length vec)]
         [new-vec (#%make-vector (fx+ 1 len))])
    (hamt-vector-copy! new-vec 0 vec 0 idx)
    (hamt-vector-set! new-vec idx child)
    (hamt-vector-copy! new-vec (fx+ 1 idx) vec idx len)
    new-vec))

(define (vector-append vec idx child)
  (let* ([len (#%vector-length vec)]
         [new-vec (#%make-vector (fx+ 1 len))])
    (hamt-vector-copy! new-vec 0 vec 0 len)
    (hamt-vector-set! new-vec len child)
    new-vec))

(define (vector-remove vec idx)
  (let* ([len (#%vector-length vec)]
         [new-vec (#%make-vector (fx- len 1))])
    (hamt-vector-copy! new-vec 0 vec 0 idx)
    (hamt-vector-copy! new-vec idx vec (fx+ 1 idx) len)
    new-vec))

;;

(define-record-type hamt
  [fields (immutable eqtype)
          (mutable root)]
  [nongenerative #{hamt kt3t3eb6ndw7a3l7l1wtmuxsh-3}]
  [sealed #t])

(define empty-hash (make-hamt 'equal empty-hamt-node))
(define empty-hasheqv (make-hamt 'eqv empty-hamt-node))
(define empty-hasheq (make-hamt 'eq empty-hamt-node))

(define (make-hamt-shell eqtype)
  (make-hamt eqtype empty-hamt-node))

(define (hamt-shell-sync! dst src)
  (hamt-root-set! dst (hamt-root src)))

(define (hamt-equal? h) (eq? 'equal (hamt-eqtype h)))
(define (hamt-eqv? h) (eq? 'eqv (hamt-eqtype h)))
(define (hamt-eq? h) (eq? 'eq (hamt-eqtype h)))

(define (hamt-count h)
  (hamt-node-count (hamt-root h)))

(define (hamt-ref h key default)
  (let ([eqtype (hamt-eqtype h)])
    (hamt-bitmap-node-ref (hamt-root h)
                          (compute-hash eqtype key)
                          key
                          cdr
                          default
                          eqtype
                          0)))

(define (hamt-ref-key h key default)
  (let ([eqtype (hamt-eqtype h)])
    (hamt-bitmap-node-ref (hamt-root h)
                          (compute-hash eqtype key)
                          key
                          car
                          default
                          eqtype
                          0)))

(define (hamt-set h key val)
  (let ([eqtype (hamt-eqtype h)])
    (make-hamt
     eqtype
     (hamt-bitmap-node-set (hamt-root h)
                           (compute-hash eqtype key)
                           key
                           val
                           eqtype))))

(define (hamt-remove h key)
  (let ([eqtype (hamt-eqtype h)])
    (make-hamt
     eqtype
     (hamt-bitmap-node-remove (hamt-root h)
                              (compute-hash eqtype key)
                              key
                              eqtype))))

(define (hamt=? a b val=?)
  (hamt-node=? (hamt-root a)
               (hamt-root b)
               (hamt-eqtype a)
               val=?))

(define (hamt-hash-code h compute-hash)
  (hamt-node-hash-code (hamt-root h) compute-hash 0))

(define (hamt-keys-subset? a b)
  (hamt-node-keys-subset?/bitmap-to-bitmap (hamt-root a)
                                           (hamt-root b)
                                           (hamt-eqtype a)
                                           0))

(define ignored/hamt
  (begin
    ;; Go through generic `hash` versions to support `a`
    ;; and `b` as impersonated hash tables
    (record-type-equal-procedure (record-type-descriptor hamt)
                                 (lambda (a b eql?)
                                   (hash=? a b eql?)))
    (record-type-hash-procedure (record-type-descriptor hamt)
                                (lambda (a hash)
                                  (hash-hash-code a hash)))))

(define (hamt-fold h nil proc)
  (let loop ([pos (unsafe-hamt-iterate-first h)] [nil nil])
    (cond
     [pos
      (let ([pair (unsafe-hamt-iterate-pair h pos)])
        (loop (unsafe-hamt-iterate-next h pos)
              (proc (car pair) (cdr pair) nil)))]
     [else
      nil])))

(define (hamt-for-each h proc)
  (hamt-fold h (void) (lambda (k v _) (|#%app| proc k v) (void))))

(define (hamt-map h proc)
  (hamt-fold h '() (lambda (k v xs) (cons (|#%app| proc k v) xs))))

;;;
;; intmap-compat layer
(define intmap? hamt?)
(define intmap-count hamt-count)
(define intmap-ref hamt-ref)
(define intmap-ref-key hamt-ref-key)
(define intmap-set hamt-set)
(define intmap-remove hamt-remove)
(define intmap-eq? hamt-eq?)
(define intmap-eqv? hamt-eqv?)
(define intmap-equal? hamt-equal?)
(define intmap-iterate-first hamt-iterate-first)
(define intmap-iterate-next hamt-iterate-next)
(define intmap-iterate-pair hamt-iterate-pair)
(define intmap-iterate-key hamt-iterate-key)
(define intmap-iterate-value hamt-iterate-value)
(define intmap-iterate-key+value hamt-iterate-key+value)
(define unsafe-intmap-iterate-first unsafe-hamt-iterate-first)
(define unsafe-intmap-iterate-next unsafe-hamt-iterate-next)
(define unsafe-intmap-iterate-pair unsafe-hamt-iterate-pair)
(define unsafe-intmap-iterate-key unsafe-hamt-iterate-key)
(define unsafe-intmap-iterate-value unsafe-hamt-iterate-value)
(define unsafe-intmap-iterate-key+value unsafe-hamt-iterate-key+value)
(define intmap-for-each hamt-for-each)
(define intmap-map hamt-map)
(define intmap-keys-subset? hamt-keys-subset?)
(define intmap=? hamt=?)
(define intmap-hash-code hamt-hash-code)
(define make-intmap-shell make-hamt-shell)
(define intmap-shell-sync! hamt-shell-sync!)
(define immutable-hash? hamt?)
