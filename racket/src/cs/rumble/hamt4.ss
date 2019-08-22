(define-record-type hamt-node
  [fields (immutable data)
          (immutable count)]
  [nongenerative #{hamt-node ewcskbb4x0re4lncf7sr81t56-0}])

(define-record-type hamt-bitmap-node
  [parent hamt-node]
  [fields (immutable keymap)
          (immutable childmap)]
  [nongenerative #{hamt-node ewcskbb4x0re4lncf7sr81t56-1}])

(define-record-type hamt-bitmap-node/vals
  [parent hamt-bitmap-node]
  [nongenerative #{hamt-node ewcskbb4x0re4lncf7sr81t56-11}]
  [sealed #t])

(define-record-type hamt-bitmap-node/no-vals
  [parent hamt-bitmap-node]
  [nongenerative #{hamt-node ewcskbb4x0re4lncf7sr81t56-12}]
  [sealed #t])

(define-record-type hamt-collision-node
  [parent hamt-node]
  [fields (immutable hash)]
  [nongenerative #{hamt-node ewcskbb4x0re4lncf7sr81t56-2}]
  [sealed #t])

(define empty-hamt-node
  (make-hamt-bitmap-node/no-vals (vector) 0 0 0))

(define bit-partition-width 5)
(define bit-partition-mask #b11111)
(define hash-code-length
  (fxbit-count (most-positive-fixnum)))


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

(define hamt-popcount popcount32)

(define (descend shift)
  (fx+ bit-partition-width shift))

(define (hamt-bitmap-node-ref node hash key kons default eqtype shift)
  (let loop ([node node] [shift shift])
    (let ([bit (hash+shift->bit hash shift)]
          [keymap (hamt-bitmap-node-keymap node)]
          [childmap (hamt-bitmap-node-childmap node)])
      (cond
       [(bitmap-has-bit? keymap bit)
        (let* ([idx (bitmap+bit->index keymap bit)]
               [test-key (bitmap-key-ref node idx)])
          (if (key=? eqtype key test-key)
              (kons test-key (bitmap-val-ref node idx))
              default))]
       [(bitmap-has-bit? childmap bit)
        (let* ([idx (bitmap+bit->index childmap bit)]
               [child (bitmap-child-ref node idx)])
          (cond
           [(hamt-bitmap-node? child)
            (loop child (descend shift))]
           [(fx= hash (hamt-collision-node-hash child))
            (hamt-collision-node-ref child key kons default eqtype)]
           [else
            default]))]
       [else
        default]))))

(define (hamt-bitmap-node-set node hash key val eqtype shift)
  (let loop ([node node] [shift shift])
    (let ([bit (hash+shift->bit hash shift)]
          [keymap (hamt-bitmap-node-keymap node)]
          [childmap (hamt-bitmap-node-childmap node)])
      (cond
       [(bitmap-has-bit? keymap bit)
        (let* ([idx (bitmap+bit->index keymap bit)]
               [test-key (bitmap-key-ref node idx)])
          (cond
           [(key=? eqtype key test-key)
            (hamt-bitmap-node-replace-k/v node idx key val)]
           [else
            (let ([old-val (bitmap-val-ref node idx)]
                  [old-hash (compute-hash eqtype test-key)])
              (let ([new-child (hamt-node-merge old-hash test-key old-val
                                                hash key val
                                                eqtype (descend shift))])
                (hamt-bitmap-node-migrate->child node bit idx new-child)))]))]
       [(bitmap-has-bit? childmap bit)
        (let* ([idx (bitmap+bit->index childmap bit)]
               [child (bitmap-child-ref node idx)]
               [new-child (if (hamt-bitmap-node? child)
                              (loop child (descend shift))
                              (hamt-collision-node-set child key val eqtype))])
          (hamt-bitmap-node-replace-child node idx child new-child))]
       [else
        (hamt-bitmap-node-add-k/v node bit key val)]))))

(define (hamt-bitmap-node-remove node hash key eqtype shift)
  (let loop ([node node] [shift shift])
    (let ([bit (hash+shift->bit hash shift)]
          [keymap (hamt-bitmap-node-keymap node)]
          [childmap (hamt-bitmap-node-childmap node)])
      (cond
       [(bitmap-has-bit? keymap bit)
        (let* ([idx (bitmap+bit->index keymap bit)]
               [test-key (bitmap-key-ref node idx)])
          (cond
           [(key=? eqtype key test-key)
            (cond
             [(and (fx= 0 childmap)
                   (fx= 2 (hamt-popcount keymap)))
              ;; Create a singleton node. If this doesn't become the new root,
              ;; its contents will be unpacked further up the tree.
              (let ([new-keymap (if (fx= 0 shift)
                                    (fxxor keymap bit)
                                    (hash+shift->bit hash 0))]
                    [other-idx (if (fx= 0 idx) 1 0)])
                (let ([k (bitmap-key-ref node other-idx)]
                      [v (bitmap-val-ref node other-idx)])
                  (if (eq? #t v)
                      (make-hamt-bitmap-node/no-vals (vector k) 1 new-keymap 0)
                      (make-hamt-bitmap-node/vals (vector k v) 1 new-keymap 0))))]
             [else
              (hamt-bitmap-node-remove-k/v node bit idx)])]
           [else
            node]))]
       [(bitmap-has-bit? childmap bit)
        (let* ([idx (bitmap+bit->index childmap bit)]
               [child (bitmap-child-ref node idx)]
               [new-child (if (hamt-bitmap-node? child)
                              (loop child (descend shift))
                              (hamt-collision-node-remove child hash key eqtype))])
          (cond
           [(fx= 1 (hamt-node-count new-child))
            (if (and (fx= 0 keymap) (fx= childmap bit))
                new-child
                (hamt-bitmap-node-migrate->k/v node bit idx new-child))]
           [else
            (hamt-bitmap-node-replace-child node idx child new-child)]))]
       [else
        node]))))

(define (bitmap-key-ref node idx)
  (if (hamt-bitmap-node/vals? node)
      (#%vector-ref (hamt-node-data node) (fx* 2 idx))
      (#%vector-ref (hamt-node-data node) idx)))

(define (bitmap-val-ref node idx)
  (if (hamt-bitmap-node/vals? node)
      (#%vector-ref (hamt-node-data node) (fx+ 1 (fx* 2 idx)))
      #t))

(define (bitmap-child-ref node idx)
  (let ([data (hamt-node-data node)])
    (#%vector-ref data (fx- (#%vector-length data) idx 1))))

(define (hamt-collision-node-ref node key kons default eqtype)
  (let ([idx (hamt-collision-node-index node key eqtype)]
        [data (hamt-node-data node)])
    (if idx
        (kons (#%vector-ref data idx)
              (#%vector-ref data (fx+ 1 idx)))
        default)))

(define (hamt-collision-node-set node key val eqtype)
  (let ([idx (hamt-collision-node-index node key eqtype)]
        [data (hamt-node-data node)])
    (cond
     [idx
      (let ([new-data (#%vector-copy data)])
        (#%vector-set! new-data idx key)
        (#%vector-set! new-data (fx+ 1 idx) val)
        (make-hamt-collision-node new-data
                                  (hamt-node-count node)
                                  (hamt-collision-node-hash node)))]
     [else
      (let* ([len (#%vector-length data)]
             [new-data (#%make-vector (fx+ 2 len))])
        (hamt-vector-copy! new-data 0 data 0 len)
        (#%vector-set! new-data len key)
        (#%vector-set! new-data (fx+ 1 len) val)
        (make-hamt-collision-node new-data
                                  (fx+ 1 (hamt-node-count node))
                                  (hamt-collision-node-hash node)))])))

(define (hamt-collision-node-remove node hash key eqtype)
  (cond
   [(fx= hash (hamt-collision-node-hash node))
    (let ([idx (hamt-collision-node-index node key eqtype)])
      (cond
       [idx
        (let ([data (hamt-node-data node)])
          (cond
           [(fx= 2 (hamt-node-count node))
            ;; Build a singleton node
            (let ([other-idx (if (fx= 0 idx) 2 0)])
              (hamt-bitmap-node-set empty-hamt-node
                                    hash
                                    (#%vector-ref data other-idx)
                                    (#%vector-ref data (fx+ 1 other-idx))
                                    eqtype
                                    0))]
           [else
            (let* ([len (#%vector-length data)]
                   [new-data (#%make-vector (fx- len 2))])
              (hamt-vector-copy! new-data 0 data 0 idx)
              (hamt-vector-copy! new-data idx data (fx+ 2 idx) len)
              (make-hamt-collision-node new-data
                                        (fx- (hamt-node-count node) 1)
                                        hash))]))]
       [else
        node]))]
   [else
    node]))

(define (hamt-collision-node-index node key eqtype)
  (let ([data (hamt-node-data node)])
    (let loop ([i (fx- (#%vector-length data) 2)])
      (and
       (fx>= i 0)
       (let ([test-key (#%vector-ref data i)])
         (if (key=? eqtype key test-key)
             i
             (loop (fx- i 2))))))))

(define (hamt-node-merge hash1 key1 val1 hash2 key2 val2 eqtype shift)
  (cond
   [(fx>= shift hash-code-length)
    (make-hamt-collision-node (vector key1 val1 key2 val2) 2 hash1)]
   [else
    (let ([mask1 (hash+shift->mask hash1 shift)]
          [mask2 (hash+shift->mask hash2 shift)])
      (cond
       [(fx= mask1 mask2)
        (let ([child (hamt-node-merge hash1 key1 val1 hash2 key2 val2 eqtype (descend shift))])
          (make-hamt-bitmap-node/no-vals (vector child)
                                         (hamt-node-count child)
                                         0
                                         (mask->bit mask1)))]
       [else
        (let ([keymap (fxior (mask->bit mask1) (mask->bit mask2))])
          (cond
           [(and (eq? #t val1) (eq? #t val2))
            (if (fx< mask1 mask2)
                (make-hamt-bitmap-node/no-vals (vector key1 key2) 2 keymap 0)
                (make-hamt-bitmap-node/no-vals (vector key2 key1) 2 keymap 0))]
           [else
            (if (fx< mask1 mask2)
                (make-hamt-bitmap-node/vals (vector key1 val1 key2 val2) 2 keymap 0)
                (make-hamt-bitmap-node/vals (vector key2 val2 key1 val1) 2 keymap 0))]))]))]))


(define (hamt-bitmap-node-replace-k/v node idx key val)
  (let ([old-data (hamt-node-data node)])
    (cond
     [(hamt-bitmap-node/no-vals? node)
      (cond
       [(eq? val #t)
        ;; no-vals -> no-vals
        (let ([new-data (#%vector-copy old-data)])
          (#%vector-set! new-data idx key)

          (make-hamt-bitmap-node/no-vals
           new-data
           (hamt-node-count node)
           (hamt-bitmap-node-keymap node)
           (hamt-bitmap-node-childmap node)))]
       [else
        ;; no-vals -> vals
        ;; slow path: need to reify all the #t values
        (let* ([old-len (#%vector-length old-data)]
               [key-count (bitmap-key-count node)]
               [new-len (fx+ old-len key-count)]
               [new-data (#%make-vector new-len)])
          (let loop ([i 0])
            (cond
             [(fx< i key-count)
              (let ([j (fx* 2 i)])
                (cond
                 [(fx= i idx)
                  (#%vector-set! new-data j key)
                  (#%vector-set! new-data (fx+ 1 j) val)]
                 [else
                  (#%vector-set! new-data j (#%vector-ref old-data i))
                  (#%vector-set! new-data (fx+ 1 j) #t)])
                (loop (fx+ i 1)))]
             [else
              (hamt-vector-copy! new-data (fx* 2 i) old-data key-count old-len)]))

          (make-hamt-bitmap-node/vals
           new-data
           (hamt-node-count node)
           (hamt-bitmap-node-keymap node)
           (hamt-bitmap-node-childmap node)))])]
     [else
      ;; vals -> vals
      (let ([new-data (#%vector-copy old-data)])
        (let ([j (fx* 2 idx)])
          (#%vector-set! new-data j key)
          (#%vector-set! new-data (fx+ 1 j) val))

        (make-hamt-bitmap-node/vals
         new-data
         (hamt-node-count node)
         (hamt-bitmap-node-keymap node)
         (hamt-bitmap-node-childmap node)))])))

(define (hamt-bitmap-node-migrate->child node bit key-idx child)
  ;; removing a k/v pair and adding a child
  (let ([keymap (hamt-bitmap-node-keymap node)]
        [childmap (hamt-bitmap-node-childmap node)]
        [old-data (hamt-node-data node)])
    (let ([len (#%vector-length old-data)]
          [child-idx (bitmap+bit->index childmap bit)])
      (cond
       [(hamt-bitmap-node/no-vals? node)
        (let ([new-data (#%make-vector len)]
              [new-idx (fx- len child-idx 1)])
          (hamt-vector-copy! new-data 0 old-data 0 key-idx)
          (hamt-vector-copy! new-data key-idx
                             old-data (fx+ 1 key-idx)
                             (fx+ new-idx 1))
          (#%vector-set! new-data new-idx child)
          (hamt-vector-copy! new-data (fx+ 1 new-idx) old-data (fx+ 1 new-idx) len)

          (make-hamt-bitmap-node/no-vals new-data
                                         (fx+ 1 (hamt-node-count node))
                                         (fxxor keymap bit)
                                         (fxior childmap bit)))]
       [else
        (let ([new-data (#%make-vector (fx+ 1 (fx- len 2)))]
              [old-idx (fx* 2 key-idx)]
              [new-idx (fx- len child-idx 2)])
          (hamt-vector-copy! new-data 0 old-data 0 old-idx)
          (hamt-vector-copy! new-data old-idx
                             old-data (fx+ 2 old-idx)
                             (fx+ 2 new-idx))
          (#%vector-set! new-data new-idx child)
          (hamt-vector-copy! new-data (fx+ 1 new-idx) old-data (fx+ 2 new-idx) len)

          (make-hamt-bitmap-node/vals new-data
                                      (fx+ 1 (hamt-node-count node))
                                      (fxxor keymap bit)
                                      (fxior childmap bit)))]))))

(define (hamt-bitmap-node-replace-child node idx old-child new-child)
  (let* ([old-data (hamt-node-data node)]
         [new-data (#%vector-copy old-data)])
    (#%vector-set! new-data
                   (fx- (#%vector-length old-data) idx 1)
                   new-child)

    (let ([new-count (fx+ (hamt-node-count node)
                          (fx- (hamt-node-count new-child)
                               (hamt-node-count old-child)))]
          [keymap (hamt-bitmap-node-keymap node)]
          [childmap (hamt-bitmap-node-childmap node)])
      (if (hamt-bitmap-node/no-vals? node)
          (make-hamt-bitmap-node/no-vals new-data new-count keymap childmap)
          (make-hamt-bitmap-node/vals new-data new-count keymap childmap)))))

(define (hamt-bitmap-node-add-k/v node bit key val)
  (let ([old-data (hamt-node-data node)]
        [keymap (hamt-bitmap-node-keymap node)])
    (let ([len (#%vector-length old-data)]
          [idx (bitmap+bit->index keymap bit)])
      (cond
       [(hamt-bitmap-node/no-vals? node)
        (cond
         [(eq? #t val)
          ;; no-vals -> no-vals
          (let ([new-data (#%make-vector (fx+ 1 len))])
            (hamt-vector-copy! new-data 0 old-data 0 idx)
            (#%vector-set! new-data idx key)
            (hamt-vector-copy! new-data (fx+ 1 idx) old-data idx len)

            (make-hamt-bitmap-node/no-vals new-data
                                           (fx+ 1 (hamt-node-count node))
                                           (fxior keymap bit)
                                           (hamt-bitmap-node-childmap node)))]
         [else
          ;; no-vals -> vals
          ;; slow path: reify #t values
          (let* ([key-count (hamt-popcount keymap)]
                 [new-len (fx+ len key-count 2)]
                 [new-data (#%make-vector new-len)])
            (let loop ([i 0])
              (cond
               [(fx< i idx)
                (#%vector-set! new-data (fx* 2 i) (#%vector-ref old-data i))
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) #t)
                (loop (fx+ i 1))]
               [(fx= i idx)
                (#%vector-set! new-data (fx* 2 i) key)
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) val)
                (loop (fx+ 1 i))]
               [(fx<= i key-count)
                (#%vector-set! new-data (fx* 2 i) (#%vector-ref old-data (fx- i 1)))
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) #t)
                (loop (fx+ i 1))]
               [else
                (hamt-vector-copy! new-data (fx* 2 i) old-data key-count len)]))

            (make-hamt-bitmap-node/vals new-data
                                        (fx+ 1 (hamt-node-count node))
                                        (fxior keymap bit)
                                        (hamt-bitmap-node-childmap node)))])]
       [else
        ;; vals -> vals
        (let ([new-data (#%make-vector (fx+ 2 len))]
              [i (fx* 2 idx)])
          (hamt-vector-copy! new-data 0 old-data 0 i)
          (#%vector-set! new-data i key)
          (#%vector-set! new-data (fx+ 1 i) val)
          (hamt-vector-copy! new-data (fx+ 2 i) old-data i len)

          (make-hamt-bitmap-node/vals new-data
                                      (fx+ 1 (hamt-node-count node))
                                      (fxior keymap bit)
                                      (hamt-bitmap-node-childmap node)))]))))

(define (hamt-bitmap-node-remove-k/v node bit idx)
  (let* ([old-data (hamt-node-data node)]
         [len (#%vector-length old-data)])
    (cond
     [(hamt-bitmap-node/no-vals? node)
      (let ([new-data (#%make-vector (fx- len 1))])
        (hamt-vector-copy! new-data 0 old-data 0 idx)
        (hamt-vector-copy! new-data idx old-data (fx+ 1 idx) len)

        (make-hamt-bitmap-node/no-vals new-data
                                       (fx- (hamt-node-count node) 1)
                                       (fxxor (hamt-bitmap-node-keymap node) bit)
                                       (hamt-bitmap-node-childmap node)))]
     [else
      (let ([new-data (#%make-vector (fx- len 2))]
            [i (fx* 2 idx)])
        (hamt-vector-copy! new-data 0 old-data 0 i)
        (hamt-vector-copy! new-data i old-data (fx+ 2 i) len)

        (make-hamt-bitmap-node/vals new-data
                                    (fx- (hamt-node-count node) 1)
                                    (fxxor (hamt-bitmap-node-keymap node) bit)
                                    (hamt-bitmap-node-childmap node)))])))

(define (hamt-bitmap-node-migrate->k/v node bit idx singleton)
  (let ([key (bitmap-key-ref singleton 0)]
        [val (bitmap-val-ref singleton 0)]
        [keymap (hamt-bitmap-node-keymap node)]
        [data (hamt-node-data node)])
    (let* ([len (#%vector-length data)]
           [old-idx (fx- len idx 1)] ;; physical child index
           [new-idx (bitmap+bit->index keymap bit)]) ;; logical k/v index
      (cond
       [(hamt-bitmap-node/no-vals? node)
        (cond
         [(eq? #t val)
          ;; no-vals -> no-vals
          ;; removing a child and adding a key, so no change in vector size
          (let ([new-data (#%make-vector len)])
            (hamt-vector-copy! new-data 0 data 0 new-idx)
            (#%vector-set! new-data new-idx key)
            (hamt-vector-copy! new-data (fx+ 1 new-idx) data new-idx old-idx)
            (hamt-vector-copy! new-data (fx+ 1 old-idx) data (fx+ 1 old-idx) len)

            (make-hamt-bitmap-node/no-vals
             new-data
             (fx- (hamt-node-count node) 1)
             (fxior keymap bit)
             (fxxor (hamt-bitmap-node-childmap node) bit)))]
         [else
          ;; no-vals -> vals
          ;; slow path: reify #t values
          (let* ([key-count (hamt-popcount keymap)]
                 [new-data (#%make-vector (fx- (fx+ len key-count 2) 1))])
            (let loop ([i 0])
              (cond
               [(fx< i new-idx)
                (#%vector-set! new-data (fx* 2 i) (#%vector-ref data i))
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) #t)
                (loop (fx+ 1 i))]
               [(fx= i new-idx)
                (#%vector-set! new-data (fx* 2 i) key)
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) val)
                (loop (fx+ 1 i))]
               [(fx<= i key-count)
                (#%vector-set! new-data (fx* 2 i) (#%vector-ref data (fx- i 1)))
                (#%vector-set! new-data (fx+ 1 (fx* 2 i)) #t)
                (loop (fx+ 1 i))]
               [else
                (let ([j (fx* 2 i)])
                  (hamt-vector-copy! new-data j data key-count old-idx)
                  (let ([diff (fx- old-idx key-count)])
                    (hamt-vector-copy! new-data (fx+ j diff) data (fx+ 1 old-idx) len)))]))
            (make-hamt-bitmap-node/vals
             new-data
             (fx- (hamt-node-count node) 1)
             (fxior keymap bit)
             (fxxor (hamt-bitmap-node-childmap node) bit)))])]
       [else
        ;; vals -> vals
        (let ([new-data (#%make-vector (fx- (fx+ 2 len) 1))]
              [i (fx* 2 new-idx)])
          (hamt-vector-copy! new-data 0 data 0 i)
          (#%vector-set! new-data i key)
          (#%vector-set! new-data (fx+ 1 i) val)
          (hamt-vector-copy! new-data (fx+ 2 i) data i old-idx)
          (hamt-vector-copy! new-data (fx+ 2 old-idx) data (fx+ 1 old-idx) len)

          (make-hamt-bitmap-node/vals
           new-data
           (fx- (hamt-node-count node) 1)
           (fxior keymap bit)
           (fxxor (hamt-bitmap-node-childmap node) bit)))]))))

(define (hamt-node=? a b eqtype val=?)
  (or
   (eq? a b)

   (and (hamt-bitmap-node? a)
        (hamt-bitmap-node? b)
        (hamt-bitmap-node=? a b eqtype val=?))

   (and (hamt-collision-node? a)
        (hamt-collision-node? b)
        (hamt-collision-node=? a b eqtype val=?))))

(define (hamt-bitmap-node=? a b eqtype val=?)
  (and (fx= (hamt-node-count a)
            (hamt-node-count b))
       (fx= (hamt-bitmap-node-keymap a)
            (hamt-bitmap-node-keymap b))
       (fx= (hamt-bitmap-node-childmap a)
            (hamt-bitmap-node-childmap b))
       ;; The vectors are not necessarily the same size, since
       ;; these HAMTs are not canonical w.r.t. whether values are
       ;; implicit or not.
       (let ([key-count (bitmap-key-count a)])
         (let key-loop ([i 0])
           (cond
            [(fx< i key-count)
             (and (key=? eqtype (bitmap-key-ref a i) (bitmap-key-ref b i))
                  (val=? (bitmap-val-ref a i) (bitmap-val-ref b i))
                  (key-loop (fx+ 1 i)))]
            [else
             ;; running this loop backwards keeps array accesses in order
             (let child-loop ([i (fx- (bitmap-child-count a) 1)])
               (cond
                [(fx>= i 0)
                 (and (hamt-node=? (bitmap-child-ref a i)
                                   (bitmap-child-ref b i)
                                   eqtype
                                   val=?)
                      (child-loop (fx- i 1)))]
                [else
                 #t]))])))))

(define (hamt-collision-node=? a b eqtype val=?)
  (and
   (fx= (hamt-collision-node-hash a) (hamt-collision-node-hash b))
   (fx= (hamt-node-count a) (hamt-node-count b))

   (let ([data-a (hamt-node-data a)])
     (let loop ([i (fx- (#%vector-length data-a) 2)])
       (cond
        [(fx>= i 0)
         (let* ([key-a (#%vector-ref data-a i)]
                [pair-b (hamt-collision-node-ref b key-a cons #f eqtype)])
           (and pair-b
                (val=? (#%vector-ref data-a (fx+ 1 i)) (cdr pair-b))
                (loop (fx- i 2))))]
        [else
         #t])))))

(define (hamt-node-hash-code node compute-hash hash)
  (cond
   [(hamt-bitmap-node? node)
    (let ([key-count (bitmap-key-count node)]
          [keymap (hamt-bitmap-node-keymap node)]
          [childmap (hamt-bitmap-node-childmap node)])
      (let* ([hash (hash-code-combine hash keymap)]
             [hash (hash-code-combine hash childmap)])
        (let key-loop ([i 0] [hash hash])
          (cond
           [(fx< i key-count)
            (let ([val (bitmap-val-ref node i)])
              (key-loop (fx+ 1 i) (hash-code-combine hash (compute-hash val))))]
           [else
            (let child-loop ([i (fx- (bitmap-child-count node) 1)] [hash hash])
              (cond
               [(fx>= i 0)
                (let* ([child (bitmap-child-ref node i)]
                       [hash (hamt-node-hash-code child compute-hash hash)])
                  (child-loop (fx- i 1) hash))]
               [else
                hash]))]))))]
   [else
    (hash-code-combine hash (hamt-collision-node-hash node))]))

(define (hamt-node-keys-subset? a b eqtype shift)
  (or
   (eq? a b)
   (and
    (fx<= (hamt-node-count a)
          (hamt-node-count b))
    (cond
     [(and (hamt-bitmap-node? a)
           (hamt-bitmap-node? b))
      (hamt-bitmap-node-keys-subset? a b eqtype shift)]
     [else
      (let loop ([pos (hamt-node-unsafe-iterate-first a #f)])
        (or (not pos)
            (let* ([key (unsafe-hamt-iterate-key #f pos)]
                   [hash (compute-hash eqtype key)])
              (and
               (if (hamt-bitmap-node? b)
                   (hamt-bitmap-node-ref b hash key (lambda (k v) #t) #f eqtype shift)
                   (hamt-collision-node-ref b key (lambda (k v) #t) #f eqtype))
               (loop (hamt-node-unsafe-iterate-next pos))))))]))))

(define (hamt-bitmap-node-keys-subset? a b eqtype shift)
  (let ([km-a (hamt-bitmap-node-keymap a)]
        [cm-a (hamt-bitmap-node-childmap a)]
        [km-b (hamt-bitmap-node-keymap b)]
        [cm-b (hamt-bitmap-node-childmap b)])
    (and
     (let ([bm-a (fxior km-a cm-a)]
           [bm-b (fxior km-b cm-b)])
       (and
        (fx= bm-a (fxand bm-a bm-b))

        (let loop ([bm-a bm-a] [bit 0] [aki 0] [bki 0] [aci 0] [bci 0])
          (cond
           [(fx= 0 bm-a)
            #t]
           [(fxbit-set? km-a bit)
            (cond
             [(fxbit-set? km-b bit)
              (and
               (key=? eqtype (bitmap-key-ref a aki) (bitmap-key-ref b bki))
               (loop (fxsrl bm-a 1) (fx+ 1 bit) (fx+ 1 aki) (fx+ 1 bki) aci bci))]
             [else
              (let ([child (bitmap-child-ref b bci)]
                    [key (bitmap-key-ref a aki)])
                (and
                 (cond
                  [(hamt-bitmap-node? child)
                   (let ([hash (compute-hash eqtype key)])
                     (hamt-bitmap-node-ref child hash key (lambda (x y) #t) #f eqtype (descend shift)))]
                  [else
                   (hamt-collision-node-ref child key (lambda (x y) #t) #f eqtype)])
                 (loop (fxsrl bm-a 1) (fx+ 1 bit) (fx+ 1 aki) bki aci (fx+ 1 bci))))])]
           [(fxbit-set? cm-a bit)
            (and
             (fxbit-set? cm-b bit)
             (hamt-node-keys-subset? (bitmap-child-ref a aci)
                                     (bitmap-child-ref b bci)
                                     eqtype
                                     (descend shift))
             (loop (fxsrl bm-a 1) (fx+ 1 bit) aki bki (fx+ 1 aci) (fx+ 1 bci)))]
           [(fxbit-set? km-b bit)
            (loop (fxsrl bm-a 1) (fx+ 1 bit) aki (fx+ 1 bki) aci bci)]
           [(fxbit-set? cm-b bit)
            (loop (fxsrl bm-a 1) (fx+ 1 bit) aki bki aci (fx+ 1 bci))]
           [else
            (loop (fxsrl bm-a 1) (fx+ 1 bit) aki bki aci bci)])))))))

(define (hamt-bitmap-node-nth node pos kons fail)
  (let ([key-count (bitmap-key-count node)])
    (cond
     [(fx< pos key-count)
      (kons (bitmap-key-ref node pos)
            (bitmap-val-ref node pos))]
     [else
      (let loop ([i (fx- (bitmap-child-count node) 1)] [pos (fx- pos key-count)])
        (cond
         [(fx>= i 0)
          (let* ([child (bitmap-child-ref node i)]
                 [count (hamt-node-count child)])
            (cond
             [(fx< pos count)
              (cond
               [(hamt-bitmap-node? child)
                (hamt-bitmap-node-nth child pos kons fail)]
               [else
                (let ([data (hamt-node-data child)])
                  (kons (#%vector-ref data (fx* 2 pos))
                        (#%vector-ref data (fx+ 1 (fx* 2 pos)))))])]
             [else
              (loop (fx- i 1) (fx- pos count))]))]
         [else
          fail]))])))

(define (hamt-iterate-first h)
  (and (fx> (hamt-count h) 0)
       0))

(define (hamt-iterate-next h pos)
  (let ([pos (fx+ 1 pos)])
    (and (fx< pos (hamt-count h))
         pos)))

(define (hamt-iterate-key h pos fail)
  (hamt-bitmap-node-nth (hamt-root h) pos (lambda (k _) k) fail))

(define (hamt-iterate-value h pos fail)
  (hamt-bitmap-node-nth (hamt-root h) pos (lambda (_ v) v) fail))

(define (hamt-iterate-pair h pos fail)
  (hamt-bitmap-node-nth (hamt-root h) pos cons fail))

(define (hamt-iterate-key+value h pos fail)
  (hamt-bitmap-node-nth (hamt-root h) pos values fail))

(define-record-type hamt-position
  [fields (immutable node)
          (immutable index)
          (immutable next)]
  [nongenerative #{hamt-position minvrn6f4rgjj0lifsv4vogyz-0}]
  [sealed #f])

(define-record-type hamt-position/key
  [parent hamt-position]
  [fields (immutable length)]
  [nongenerative #{hamt-position minvrn6f4rgjj0lifsv4vogyz-1}]
  [sealed #t])

(define-record-type hamt-position/child
  [parent hamt-position]
  [fields]
  [nongenerative #{hamt-position minvrn6f4rgjj0lifsv4vogyz-2}]
  [sealed #t])

(define-record-type hamt-position/collision
  [parent hamt-position]
  [fields]
  [nongenerative #{hamt-position minvrn6f4rgjj0lifsv4vogyz-3}]
  [sealed #t])

(define (hamt-node-unsafe-iterate-first node next)
  (cond
   [(hamt-bitmap-node? node)
    (cond
     [(fx> (hamt-bitmap-node-keymap node) 0)
      (make-hamt-position/key node 0 next (bitmap-key-count node))]
     [else
      (let* ([idx (fx- (bitmap-child-count node) 1)]
             [next (make-hamt-position/child node idx next)])
        (hamt-node-unsafe-iterate-first (bitmap-child-ref node idx) next))])]
   [else
    (let ([idx (fx- (#%vector-length (hamt-node-data node)) 2)])
      (make-hamt-position/collision node idx next))]))

(define (hamt-node-unsafe-iterate-next pos)
  (cond
   [pos
    (let ([node (hamt-position-node pos)]
          [idx (hamt-position-index pos)]
          [next (hamt-position-next pos)])
      (cond
       [(hamt-position/key? pos)
        (let ([len (hamt-position/key-length pos)]
              [idx (fx+ 1 idx)])
          (cond
           [(fx= idx len)
            (cond
             [(fx> (hamt-bitmap-node-childmap node) 0)
              (let* ([idx (fx- (bitmap-child-count node) 1)]
                     [next (make-hamt-position/child node idx next)])
                (hamt-node-unsafe-iterate-first (bitmap-child-ref node idx) next))]
             [else
              (hamt-node-unsafe-iterate-next next)])]
           [else
            (make-hamt-position/key node idx next len)]))]
       [(hamt-position/child? pos)
        (cond
         [(fx= 0 idx)
          (hamt-node-unsafe-iterate-next next)]
         [else
          (let* ([idx (fx- idx 1)]
                 [child (bitmap-child-ref node idx)]
                 [pos (make-hamt-position/child node idx next)])
            (hamt-node-unsafe-iterate-first child pos))])]
       [else
        (cond
         [(fx= 0 idx)
          (hamt-node-unsafe-iterate-next next)]
         [else
          (make-hamt-position/collision node (fx- idx 2) next)])]))]
   [else
    #f]))

(define (unsafe-hamt-iterate-first h)
  (and (fx> (hamt-count h) 0)
       (hamt-node-unsafe-iterate-first (hamt-root h) #f)))

(define (unsafe-hamt-iterate-next h pos)
  (hamt-node-unsafe-iterate-next pos))

(define-syntax-rule (define-unsafe-hamt-iterator (name pos) key-get collision-get)
  (define (name _ pos)
    (let ([node (hamt-position-node pos)]
          [idx (hamt-position-index pos)])
      (cond
       [(hamt-position/key? pos)
        (key-get node idx)]
       [else
        (collision-get node idx)]))))

(define-unsafe-hamt-iterator (unsafe-hamt-iterate-key pos)
  (lambda (node idx) (bitmap-key-ref node idx))
  (lambda (node idx) (#%vector-ref (hamt-node-data node) idx)))

(define-unsafe-hamt-iterator (unsafe-hamt-iterate-value pos)
  (lambda (node idx) (bitmap-val-ref node idx))
  (lambda (node idx) (#%vector-ref (hamt-node-data node) (fx+ 1 idx))))

(define-unsafe-hamt-iterator (unsafe-hamt-iterate-key+value pos)
  (lambda (node idx)
    (values (bitmap-key-ref node idx)
            (bitmap-val-ref node idx)))
  (lambda (node idx)
    (let ([data (hamt-node-data node)])
      (values (#%vector-ref data idx)
              (#%vector-ref data (fx+ 1 idx))))))

(define (unsafe-hamt-iterate-pair h pos)
  (let-values ([(k v) (unsafe-hamt-iterate-key+value h pos)])
    (cons k v)))

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

(define (bitmap-key-count node)
  (hamt-popcount (hamt-bitmap-node-keymap node)))

(define (bitmap-child-count node)
  (hamt-popcount (hamt-bitmap-node-childmap node)))

(define (hamt-vector-copy! dst dst-start src src-start src-end)
  (#%$ptr-copy! src
                (fx+ vector-data-disp
                     (fx* ptr-bytes src-start))
                dst
                (fx+ vector-data-disp
                     (fx* ptr-bytes dst-start))
                (fx- src-end src-start)))

#;(define (hamt-vector-copy! dst dst-start src src-start src-end)
  (vector*-copy! dst dst-start src src-start src-end))

(define vector-data-disp 9)
(define ptr-bytes 8)

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
                          (lambda (_ v) v)
                          default
                          eqtype
                          0)))

(define (hamt-ref-key h key default)
  (let ([eqtype (hamt-eqtype h)])
    (hamt-bitmap-node-ref (hamt-root h)
                          (compute-hash eqtype key)
                          key
                          (lambda (k _) k)
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
                           eqtype
                           0))))

(define (hamt-remove h key)
  (let* ([eqtype (hamt-eqtype h)]
         [new-root
          (hamt-bitmap-node-remove
           (hamt-root h)
           (compute-hash eqtype key)
           key
           eqtype
           0)])
    (if (fx= 0 (hamt-node-count new-root))
        (case eqtype
          [(eq) empty-hasheq]
          [(eqv) empty-hasheqv]
          [else empty-hash])
        (make-hamt eqtype new-root))))

(define (hamt=? a b val=?)
  (and
   (eq? (hamt-eqtype a)
        (hamt-eqtype b))
   (hamt-node=? (hamt-root a)
                (hamt-root b)
                (hamt-eqtype a)
                val=?)))

(define (hamt-hash-code h compute-hash)
  (hamt-node-hash-code (hamt-root h) compute-hash 0))

(define (hamt-keys-subset? a b)
  (hamt-bitmap-node-keys-subset? (hamt-root a)
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
      (let-values ([(k v) (unsafe-hamt-iterate-key+value h pos)])
        (loop (unsafe-hamt-iterate-next h pos)
              (proc k v nil)))]
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
