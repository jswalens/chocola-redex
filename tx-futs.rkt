#lang racket

(require redex)
(require "clj-base.rkt")
(require "map.rkt")
(require "set.rkt")
(require "futures.rkt")
(require "tx-atomic.rkt")

(provide Ltf)

(module+ test
  (require (submod "clj-base.rkt" test))
  (require (submod "futures.rkt" test))
  (require (submod "tx-atomic.rkt" test))
  (provide (all-defined-out)))

; Language with transactions
; Figure 5 in ECOOP paper.
(define-extended-language Ltf Lt
  (σ ::= [(r v) ...])
  (spawned ::= [f ...])
  (merged  ::= [f ...])
  (tx-task ::= (f σ τ spawned merged e))
  (tx      ::= [tx-task ...])
  
  ; Same as in Lt:
  ;(P ::= [TASKS θ])
  ;(TASKS ::= (task ... TASK task ...))
  ;(TASK ::= (f E))

  (TX ::= [tx-task ... TX-TASK tx-task ...])
  (TX-TASK ::= (f σ τ spawned merged E)))

(module+ test
  ; One transaction, no conflicts
  (define example-tx-futs-1-body
    (term (let [(x (fork (ref-set r_0 (+ (deref r_0) 1))))
                (y (fork (ref-set r_1 (+ (deref r_1) 1))))]
            (+ (join x) (join y)))))
  (define example-tx-futs-1
    (inject-Lt
     (let [(r_0 (ref 0))
           (r_1 (ref 1))]
       (atomic
        ,example-tx-futs-1-body))))

  ; One transaction, with a conflict
  (define example-tx-futs-2
    (inject-Lt
     (let [(r_0 (ref 0))]
       (atomic
        (let [(x (fork (ref-set r_0 (+ (deref r_0) 1))))
                (y (fork (ref-set r_0 (+ (deref r_0) 2))))]
            (do (join x)
              (join y)
              (deref r_0)))))))

  ; Two transactions, with conflict in tx
  (define example-tx-futs-3
    (inject-Lt
     (let [(r_0 (ref 0))
           (f_0 (fork
                 (atomic
                  (let [(x (fork (ref-set r_0 (+ (deref r_0) 1))))
                        (y (fork (ref-set r_0 (+ (deref r_0) 2))))]
                    (do (join x) ; => r_0 = original + 1
                      (join y)   ; => r_0 = original + 2
                      (deref r_0)))))) ; => returns original + 2
           (f_1 (fork
                 (atomic
                  (let [(x (fork (ref-set r_0 (+ (deref r_0) 3))))
                        (y (fork (ref-set r_0 (+ (deref r_0) 4))))]
                    (do (join x) ; => r_0 = original + 3
                      (join y)   ; => r_0 = original + 4
                      (deref r_0))))))] ; => returns original + 4
       (+ (join f_0) (join f_1))))) ; = either (0+2)+(2+4)=8 or (0+4)+(4+2)=10
  
  (test-in-language? Ltf example-tx-futs-1)
  (test-in-language? Ltf example-tx-futs-2)
  (test-in-language? Ltf example-tx-futs-3))

; Reduction relation in transaction.
; Figure 5 in ECOOP paper.
(define =>tf
  (reduction-relation
   Ltf
   #:domain tx
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E e)) tx-task_1 ...]
        [tx-task_0 ... (f σ τ_1 spawned merged (in-hole E e_1)) tx-task_1 ...]
        (where (any ... [σ τ_1 e_1] any ...)
               ,(apply-reduction-relation =>t (term [σ τ e]))) ; no *
        "regular tx step")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (fork e))) tx-task_1 ...]
        [tx-task_0 ... (f σ τ (set-add spawned f_new) merged (in-hole E f_new)) (f_new (map-merge σ τ) [] [] merged e) tx-task_1 ...]
        (fresh f_new)
        "fork in tx")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (join f_2))) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        [tx-task_0 ... (f σ (map-merge τ τ_2) spawned merged_new (in-hole E v_2)) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        (where #f (set-contains? f_2 merged))
        (where #t (set-subset? spawned_2 merged_2))
        (where merged_new (set-add (set-union merged merged_2) f_2))
        "join 1")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (join f_2))) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        [tx-task_0 ... (f σ τ spawned merged (in-hole E v_2)) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        (where #t (member f_2 merged))
        "join 2")))

; Reduction relation out transaction.
; Figure 5 in ECOOP paper.
(define ->tf
  (extend-reduction-relation
   ->t ; We can extend the existing relation, as the domain in the same.
   Ltf
   #:domain p
   (--> [(in-hole TASKS (atomic e)) θ]
        [(in-hole TASKS v) θ_1]
        (where (any ... [(f_root θ τ_1 spawned_1 merged_1 v) tx-task_2 ...] any ...)
               ,(apply-reduction-relation* =>tf (term [(f_root θ [] [] [] e)]))) ; note *
        (where #t (set-subset? spawned_1 merged_1))
        (where θ_1 (map-merge θ τ_1))
        "atomic")))

(module+ test
  ; In tx: test =>tf
  (test-equal (redex-match? Ltf tx (term [(f [] [] [] [] (+ 1 1))])) #t)
  (test-->> =>tf
            (term [(f [] [] [] [] (+ 1 1))])
            (term [(f [] [] [] [] 2)]))

  ; Out tx: test ->tf
  ; Examples from base language
  (test-->> ->tf
            (inject-Lt (let [(a 1)] (+ a a)))
            (term [[(f_0 2)] []]))
  (test-->> ->tf (inject-Lt ,example-doubling) (term [((f_0 4)) ()]))
  (test-->> ->tf (inject-Lt ,example-sum-3) (term [((f_0 6)) ()]))
  (test-->> ->tf (inject-Lt ,example-base-language) (term [((f_0 9)) ()]))

  ; Examples with transactional futures
  #;(traces =>tf (term [(f [(r_1 1) (r_0 0)] [] [] [] ,example-tx-futs-1-body)]))
  #;(traces ->tf example-tx-futs-1)
  ; Passes, takes about 6 seconds
  #;(test-->> =>tf
            (term [(f       [(r_1 1) (r_0 0)] []                []  []  ,example-tx-futs-1-body)])
            (term [(f       [(r_1 1) (r_0 0)] [(r_1 2) (r_0 1)] [f_new f_new1] [f_new f_new1] 3)  ; is order of τ correct?
                   (f_new1  [(r_1 1) (r_0 0)] [(r_1 2)]         []             []             2)
                   (f_new   [(r_1 1) (r_0 0)] [(r_0 1)]         []             []             1)]))
  ; Passes, takes about 6 seconds
  #;(test-->> ->tf
            example-tx-futs-1
            (term [[(f_0 3)] [(r_new1 2) (r_new 1) (r_new1 1) (r_new 0)]]))

  ; Passes, takes about 6 seconds
  #;(test-->> ->tf
            example-tx-futs-2
            (term [[(f_0 2)] [(r_new 2) (r_new 1) (r_new 0)]]))

  ; Passes, but takes several minutes
  #;(test-->>∃ ->tf
             example-tx-futs-3
             (term [[(f_0 8) (f_new1 6) (f_new 2)]
                    [(r_new 6) (r_new 5) (r_new 2) (r_new 1) (r_new 0)]]))
  ; Tx 1 first, then 2:
  ; * r_new starts as 0
  ; * tx 1's x writes 0+1=1
  ; * tx 1's y writes 0+2=2
  ; * tx 1 returns 2         -> f_new
  ; * tx 2's x writes 2+3=5
  ; * tx 2's y writes 2+4=6
  ; * tx 2 returns 6         -> f_new1
  ; * program returns 2+6=8  -> f_0
  #;(test-->>∃ ->tf
             example-tx-futs-3
             (term [[(f_0 10) (f_new1 4) (f_new 6)]
                    [(r_new 6) (r_new 5) (r_new 4) (r_new 3) (r_new 0)]]))
  ; Tx 2 first, then 1:
  ; * r_new starts as 0
  ; * tx 2's x writes 0+3=3
  ; * tx 2's y writes 0+4=4
  ; * tx 2 returns 4         -> f_new1
  ; * tx 1's x writes 4+1=5
  ; * tx 1's y writes 4+1=6
  ; * tx 1 returns 6         -> f_new
  ; * program returns 4+6=10 -> f_0
  #;(traces ->tf example-tx-futs-3) ; visualize these results
  (print "done"))
