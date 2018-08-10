#lang racket

(require redex)
(require "clj-base.rkt")

(provide Lf ->f)

(module+ test
  (require (submod "clj-base.rkt" test))
  (provide (all-defined-out)))

; Language with futures, extends base language.
; Figure 1 in ECOOP paper.
(define-extended-language Lf Lb
  (f ::= variable-not-otherwise-mentioned)
  (v ::= ....
     f)
  (e ::= ....
     (fork e)
     (join e))
  (task ::= (f e))
  (tasks ::= (task ...)) ; map f → e
  (p ::= tasks) ; program = list of tasks
  
  (P ::= TASKS)
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (join E)))

(module+ test
  ; Inject expression `e` in the initial configuration.
  (define-syntax-rule (inject-Lf e)
    (term ((f_0 e))))

  ; Define examples and test whether they're in the language.
  (test-in-language? Lf (term ((f_0 (fork (+ 1 2))))))
  (define example-fork-join
    (inject-Lf
     (let [(double ,example-double)
           (four (fork (double 2)))]
       (join four))))
  (test-in-language? Lf example-fork-join)
  (define example-fork
    (inject-Lf
     (let [(double ,example-double)]
       (fork (double 2)))))
  (test-in-language? Lf example-fork)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-forks
    (inject-Lf
     (let [(double ,example-double)
           (four (fork (double 2)))
           (eight (fork (double 4)))]
       (+ (join four) (join eight)))))
  (test-in-language? Lf example-two-forks))

; Reduction relation for language with futures
; Figure 1 in ECOOP paper.
(define ->f
  (reduction-relation
   Lf
   #:domain p
   ; Copied from base language
   ; We cannot use extend-reduction-relation as the domain looks different.
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P ((fn [x_1 ..._n] e) v_1 ..._n))
        (in-hole P (subst [(v_1 x_1) ...] e))
        "β: function application")
   (--> (in-hole P (let [(x_0 v_0) (x_1 e_1) ...] e))
        (in-hole P (let [(x_1 (subst [(v_0 x_0)] e_1)) ...] (subst [(v_0 x_0)] e)))
        "let 1")
   (--> (in-hole P (let [] e))
        (in-hole P e)
        "let 0")
   (--> (in-hole P (do v_0 ... v_n))
        (in-hole P v_n)
        "do")
   (--> (in-hole P (if true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if false e_1 e_2))
        (in-hole P e_2)
        "if_false")
   ; New:
   (--> (task_0 ... (f_1 (in-hole E (fork e))) task_2 ...)
        (task_0 ... (f_1 (in-hole E f_new)) (f_new e) task_2 ...)
        (fresh f_new)
        "fork")
   (--> (task_0 ... (f_1 (in-hole E (join f_3))) task_2 ... (f_3 v_3) task_4 ...)
        (task_0 ... (f_1 (in-hole E v_3)) task_2 ... (f_3 v_3) task_4 ...)
        "join")))

(module+ test
  ; Returns true if lists `l1` and `l2` contain the same elements.
  (define (same-elements? l1 l2)
    (set=? (list->set l1) (list->set l2)))

  ; Test ->f
  ; Examples from base language
  (test-->> ->f (inject-Lf ,example-doubling) (term ((f_0 4))))
  (test-->> ->f (inject-Lf ,example-sum-3) (term ((f_0 6))))
  (test-->> ->f (inject-Lf ,example-base-language) (term ((f_0 9))))

  #;(traces ->f example-fork-join)
  (test-->> ->f
            #:equiv same-elements?
            example-fork-join
            (term ((f_0 4) (f_new 4))))
  #;(traces ->f example-fork)
  (test-->> ->f
            #:equiv same-elements?
            example-fork
            (term ((f_0 f_new) (f_new 4))))
  #;(traces ->f example-join)
  (test-->> ->f
            #:equiv same-elements?
            example-join
            (term ((f_0 4) (f_1 4))))
  #;(traces ->f example-two-forks)
  (test-->> ->f
            #:equiv same-elements?
            example-two-forks
            (term ((f_0 12) (f_new 4) (f_new1 8)))))

(module+ test
  (test-results))
