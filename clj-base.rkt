#lang racket

(require redex)

(provide Lb ->b subst subst-raw)

(module+ test
  (provide (all-defined-out)))

; Base language
; The syntax is inspired by Clojure. This leads to some small differences with
; Scheme, e.g. do instead of begin, fn instead of lambda.
(define-language Lb
  (c ::= nil
     bool
     number
     string)
  (bool ::= true
     false)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= c
     x
     (fn [x ...] e))
  (e ::= v
     (+ e ...)
     (- e ...)
     (= e ...)
     (not e)
     (e e ...)
     (if e e e)
     (let [(x e) ...] e) ; Note: not as in Clojure
     (do e e ...)) ; Note: only useful when adding side effects
  (p ::= e)
  
  (P ::= E)
  (E ::= hole
     (+ v ... E e ...)
     (- v ... E e ...)
     (= v ... E e ...)
     (not E)
     (v ... E e ...)
     (if E e e)
     (let [(x E) (x e) ...] e) ; TODO: allow multiple statements in let
     (do v ... E e ...)))

(module+ test
  ; Tests whether term `t` is in language `l`.
  (define-syntax-rule (test-in-language? l t)
    (test-equal (redex-match? l p t) #t))

  ; Some example programs.
  (define example-sum
    (term (+ 1 2)))
  (define example-double
    (term (fn [x] (+ x x))))
  (define example-doubling
    (term (let [(double ,example-double)] (double 2))))
  (define example-sum-3
    (term ((fn [x y z] (+ (+ x y) z)) 1 2 3)))
  (define example-base-language
    (term (let [(x 4)
                (y 5)]
            (if true
                (do
                    "nothing"
                  (+ x y))
                "error"))))

  ; Test whether examples are in languages.
  (test-in-language? Lb (term 1))
  (test-in-language? Lb example-double)
  (test-in-language? Lb example-doubling)
  (test-in-language? Lb example-sum-3)
  (test-in-language? Lb example-base-language))

; Substitute variables with their value in an expression.
(define-metafunction Lb
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x ...) any_body))
   (lambda (x_new ...)
     (subst ((any_1 x_1) ...)
            (subst-raw ((x_new x) ...) any_body)))
   (where  (x_new ...)  ,(variables-not-in (term any_body) (term (x ...)))) ]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])

(define-metafunction Lb
  subst-raw : ((x x) ...) any -> any
  [(subst-raw ((x_n1 x_o1) ... (x_new x) (x_n2 x_o2) ...) x) x_new]
  [(subst-raw ((x_n1 x_o1) ... ) x) x]
  [(subst-raw ((x_n1 x_o1) ... ) (lambda (x ...) any))
   (lambda (x ...) (subst-raw ((x_n1 x_o1) ... ) any))]
  [(subst-raw [(any_1 x_1) ... ] (any ...))
   ((subst-raw [(any_1 x_1) ... ] any) ...)]
  [(subst-raw [(any_1 x_1) ... ] any_*) any_*])

; Reduction relation for base language
(define ->b
  (reduction-relation
   Lb
   #:domain p
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P (- number ...))
        (in-hole P ,(apply - (term (number ...))))
        "-")
   (--> (in-hole P (= v_1 v_2))
        (in-hole P bool)
        (where bool ,(if (eq? (term v_1) (term v_2)) (term true) (term false)))
        "=")
   (--> (in-hole P (not true))
        (in-hole P false)
        "not_true")
   (--> (in-hole P (not false))
        (in-hole P true)
        "not_false")
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
        "if_false")))

(module+ test
  ; Test ->b
  (test-->> ->b example-sum (term 3))
  #;(traces ->b example-doubling)
  (test-->> ->b example-doubling (term 4))
  (test-->> ->b example-sum-3 (term 6))
  (test-->> ->b (term (+ 1 4 3 2)) (term 10))
  (test-->> ->b (term (- 4 3)) (term 1))
  (test-->> ->b (term (- 2 10)) (term -8))
  (test-->> ->b (term (= 1 1)) (term true))
  (test-->> ->b (term (= 1 2)) (term false))
  (test-->> ->b (term (= "abc" "abc")) (term true))
  (test-->> ->b (term (= "abc" 1)) (term false))
  (test-->> ->b (term (not true)) (term false))
  (test-->> ->b (term (not false)) (term true))
  (test-->> ->b (term (not (= "abc" 1))) (term true))
  #;(traces ->b example-base-language)
  (test-->> ->b example-base-language (term 9)))

(module+ test
  (test-results))
