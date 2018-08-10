#lang racket

(require redex)
(require "clj-base.rkt")
(require "map.rkt")
(require "futures.rkt")

(provide Lt ->t =>t)

(module+ test
  (require (submod "clj-base.rkt" test))
  (require (submod "futures.rkt" test))
  (provide (all-defined-out)))

; Language with transactions
; Figure 2 in ECOOP paper.
(define-extended-language Lt Lf
  (r ::= variable-not-otherwise-mentioned)
  (v ::= ....
     r)
  (e ::= ....
     (ref e)
     (deref e)
     (ref-set e e)
     (atomic e)
     (retry)) ; retry not in paper
  (θ ::= [(r v) ...])
  (τ ::= [(r v) ...])
  (p ::= [tasks θ]) ; program = list of tasks + heap

  (tx ::= [θ τ e])
  
  (P ::= [TASKS θ])
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (ref E)
     (deref E)
     (ref-set E e)
     (ref-set r E))

  (TX ::= [θ τ E]))

(module+ test
  ; Inject expression `e` in the initial configuration.
  (define-syntax-rule (inject-Lt e)
    (term [((f_0 e)) ()]))

  ; Some programs with transactions
  (define example-tx-body
    ; the body of a transaction, reused in different tests
    (term (do
              (ref-set a (+ (deref a) 1))
            (ref-set b (+ (deref b) 1))
            (+ (deref a) (deref b)))))
  (define example-tx-simple
    (inject-Lt
     (let [(a (ref 0))
           (b (ref 1))]
       (atomic
        ,example-tx-body))))
  (define example-tx-two-seq-tx
    (inject-Lt
     (let [(a (ref 0))
           (b (ref 1))]
       (do (atomic ,example-tx-body)
         (atomic ,example-tx-body)))))
  (define example-tx-tx-in-fork
    (inject-Lt
     (fork (atomic (+ 1 2)))))
  (define example-tx-two-par-tx
    ; determinate: order of tx's not defined, but result will always be the same
    (inject-Lt
     (let [(a (ref 0))
           (b (ref 1))
           (f (fork (atomic ,example-tx-body)))
           (g (fork (atomic ,example-tx-body)))]
       (+ (join f) (join g)))))
  (define example-tx-non-det
    ; non-determinate: different results possible
    (inject-Lt
     (let [(a (ref 0))
           (f (fork (atomic (ref-set a 1))))
           (g (fork (atomic (ref-set a 2))))]
       (do (join f)
         (join g)
         (atomic (deref a))))))
  
  (test-in-language? Lt example-tx-simple)
  (test-in-language? Lt example-tx-two-seq-tx)
  (test-in-language? Lt example-tx-tx-in-fork)
  (test-in-language? Lt example-tx-two-par-tx)
  (test-in-language? Lt example-tx-non-det))

; Reduction relations ->t and =>t for language with transactions
; Figure 2 of ECOOP paper.
(define =>t
  (reduction-relation
   Lt
   #:domain tx
   (--> [θ τ (in-hole E (ref v))]
        [θ (map-set τ r_new v) (in-hole E r_new)]
        (fresh r_new)
        "ref")
   (--> [θ τ (in-hole E (deref r))]
        [θ τ (in-hole E v)]
        (where #true (map-contains? τ r))
        (where v (map-get τ r))
        ; Unlike the paper, we split up deref into local and global, because it's easier
        "deref local")
   (--> [θ τ (in-hole E (deref r))]
        [θ τ (in-hole E v)]
        (where #false (map-contains? τ r))
        (where v (map-get θ r))
        "deref global")
   (--> [θ τ (in-hole E (ref-set r v))]
        [θ (map-set τ r v) (in-hole E v)]
        "ref-set")
   (--> [θ τ (in-hole E (atomic e))]
        [θ τ (in-hole E e)]
        "nested atomic")
   (--> [θ τ (in-hole E e)]
        [θ τ (in-hole E e_1)]
        (where (e_0 ... e_1 e_2 ...) ,(apply-reduction-relation ->b (term e))) ; no *
        "base language in tx")))

; Also Figure 2 of ECOOP paper.
(define ->t
  (extend-reduction-relation
   ->b ; we extend the base language, as ->f has a different domain
   Lt
   #:domain p
   ; Copied from ->f, but domain modified:
   (--> [(task_0 ... (f_1 (in-hole E (fork e))) task_2 ...) θ]
        [(task_0 ... (f_1 (in-hole E f_new)) (f_new e) task_2 ...) θ]
        (fresh f_new)
        "fork")
   (--> [(task_0 ... (f_1 (in-hole E (join f_3))) task_2 ... (f_3 v_3) task_4 ...) θ]
        [(task_0 ... (f_1 (in-hole E v_3)) task_2 ... (f_3 v_3) task_4 ...) θ]
        "join")
   ; New:
   (--> [(in-hole TASKS (ref v)) θ]
        [(in-hole TASKS r_new) (map-set θ r_new v)]
        (fresh r_new)
        ; not allowed in the paper, but allowed in Clojure
        "ref out tx")
   (--> [(in-hole TASKS (atomic e)) θ]
        [(in-hole TASKS v) θ_1]
        (where (any ... [θ τ_1 v] any ...)
               ,(apply-reduction-relation* =>t (term [θ () e]))) ; note *
        (where θ_1 (map-merge θ τ_1))
        ; This unfortunately breaks PLT Redex's traces...
        "atomic")))

(module+ test
  ; ref outside tx
  #;(traces ->t (inject-Lt (ref 0)))
  (test-->> ->t
            (term [((f_0 (ref 0))) ()])
            (term [((f_0 r_new)) ((r_new 0))]))

  ; =>t: things in tx
  (test-->> =>t
            (term [() () (ref 0)])
            (term [() ((r_new 0)) r_new]))
  (test-->> =>t
            (term [((a 0) (b 1)) () (deref a)]) ; look up in θ
            (term [((a 0) (b 1)) () 0]))
  (test-->> =>t
            (term [((a 0) (b 1)) ((a 2)) (deref a)]) ; look up in τ over θ
            (term [((a 0) (b 1)) ((a 2)) 2]))

  ; base language in tx
  (test-->> =>t
           (term [() () (+ 1 2)])
           (term [() () 3]))

  ; just base language (outside tx)
  (test-->> ->t
           (inject-Lt ,example-doubling)
           (term [((f_0 4)) ()]))
  (test-->> ->t
           (inject-Lt ,example-sum-3)
           (term [((f_0 6)) ()]))
  (test-->> ->t
           (inject-Lt ,example-base-language)
           (term [((f_0 9)) ()]))
  
  ; in a tx
  #;(traces =>t (term [((a 0) (b 1)) () ,example-tx-simple-tx]))
  (test-->> =>t
            (term [((a 0) (b 1)) () ,example-tx-body])
            (term [((a 0) (b 1)) ((b 2) (a 1)) 3]))

  ; atomic
  (test-->> ->t
            (term [((f_0 (atomic 5))) ()])
            (term [((f_0 5)) ()]))
  (test-->> ->t
            (term [((f_0 (atomic (deref a)))) ((a 0))])
            (term [((f_0 0)) ((a 0))]))
  (test-->> ->t
            (term [((f_0 (atomic (ref-set a 1)))) ((a 0))])
            (term [((f_0 1)) ((a 1) (a 0))])) ; TODO: overwrite instead of add?
  (test-->> ->t
            (term [((f_0 (atomic (ref-set a (+ (deref a) (+ 1 2)))))) ((a 0))])
            (term [((f_0 3)) ((a 3) (a 0))]))

  ; full example programs
  #;(traces ->t example-tx-simple)
  (test-->> ->t
            example-tx-simple
            (term [((f_0 3))
                   ((r_new1 2) (r_new 1) (r_new1 1) (r_new 0))]))

  #;(traces ->t example-tx-two-seq-tx)
  (test-->> ->t
            example-tx-two-seq-tx
            (term [((f_0 5))
                   ; a = r_new; b = r_new1
                   ((r_new1 3) (r_new 2) (r_new1 2) (r_new 1) (r_new1 1) (r_new 0))]))

  #;(traces ->t example-tx-tx-in-fork)
  (test-->> ->t
            example-tx-tx-in-fork
            (term [((f_0 f_new) (f_new 3)) ()]))

  ; There are two schedules: tx 1 executes first or tx 2 first.
  ; The end result is the same, f_0 = 8, but the results of f_new and f_new1
  ; are different.
  #;(traces ->t example-tx-two-par-tx)
  (test-->>∃ ->t
             example-tx-two-par-tx
             (term [((f_0 8)
                     (f_new1 3)
                     (f_new 5))
                    ((r_new1 3)
                     (r_new 2)
                     (r_new1 2)
                     (r_new 1)
                     (r_new1 1)
                     (r_new 0))]))
  (test-->>∃ ->t
             example-tx-two-par-tx
             (term [((f_0 8)
                     (f_new1 5)
                     (f_new 3))
                    ((r_new1 3)
                     (r_new 2)
                     (r_new1 2)
                     (r_new 1)
                     (r_new1 1)
                     (r_new 0))]))

  ; There are two possible schedules.
  ; If tx 1 executes first, then tx 2, the result is 2;
  ; if tx 2 executes first, then tx 1, the result is 1.
  #;(traces ->t example-tx-non-det)
  (test-->>∃ ->t
             example-tx-non-det
             (term [((f_0 1)
                     (f_new1 2)
                     (f_new 1))
                    ((r_new 1)
                     (r_new 2)
                     (r_new 0))]))
  (test-->>∃ ->t
             example-tx-non-det
             (term [((f_0 2)
                     (f_new1 2)
                     (f_new 1))
                    ((r_new 2)
                     (r_new 1)
                     (r_new 0))])))

(module+ test
  (test-results))
