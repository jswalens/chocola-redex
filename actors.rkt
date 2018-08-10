#lang racket

(require redex)
(require "clj-base.rkt")

(provide La ->a)

(module+ test
  (require (submod "clj-base.rkt" test))
  (provide (all-defined-out)))

; Language with actors, extends base language.
(define-extended-language La Lb
  ; actor address
  (address ::= variable-not-otherwise-mentioned)
  ; parameterized behavior
  ;(b ::= (fn [x ...] e)) ; XXX same as function
  ; actor
  (a ::= (address e e)) ; first e = currently evaluating; last e = application of behavior to its state
  ; message
  (m ::= (address address (v ...)))
  ; inboxes
  (inbox ::= (address (m ...)))
  (μ ::= (inbox ...))

  (v ::= ....
     address
     self ; special variable for actor to refer to itself -- are these values or expressions?
     same) ; special variable for become, to refer to own behavior
  (e ::= ....
     (spawn e e ...)
     (behavior [x ...] e)
     (become e e ...)
     (send e e ...)
     (receive e)) ; not to be used by the programmer directly, corresponds to idle state
  (actors ::= (a ...))
  (p ::= (actors μ)) ; program = list of actors + inboxes
  
  (P ::= (ACTORS μ))
  (ACTORS ::= (a ... ACTOR a ...))
  (ACTOR ::= (address E e))
  (E ::= ....
     (spawn v ... E e ...)
     (become v ... E e ...)
     (send E e)
     (send v E)))

(module+ test
  ; Inject behavior `e` in the initial configuration.
  ; Initial configuration contains an (empty) message from the initial actor
  ; to itself.
  (define-syntax-rule (initial-conf e)
    (term (((address_0 nil e)) ((address_0 ((address_0 address_0 ())))))))

  ; Define examples and test whether they're in the language.
  (test-in-language? La (term (((address_0 (+ 1 2) (fn [] (+ 1 2)))) ())))
  (test-in-language? La (initial-conf (fn [] ,example-doubling)))
  (define example-become-behavior
    (term (let [(b (behavior [y] (fn [] 7)))]
            (become b 5))))
  (define example-become (initial-conf (fn [] ,example-become-behavior)))
  (test-in-language? La example-become)
  (define example-spawn-behavior
    (term (let [(b (behavior [] (fn [] 7)))
                (address_1 (spawn b))]
            3)))
  (define example-spawn (initial-conf (fn [] ,example-spawn-behavior)))
  (test-in-language? La example-spawn)
  (define example-send-behavior
    (term (let [(b (behavior [] (fn [x] x)))
                (address_1 (spawn b))]
            (send address_1 5))))
  (define example-send (initial-conf (fn [] ,example-send-behavior)))
  (test-in-language? La example-send)
  (define example-counter-behavior
    (term
     (behavior
      [i]
      (fn [op arg]
          (if (= op "add")
              (become same (+ i arg))
              (if (= op "get")
                  (send arg i)
                  false))))))
  (define example-counter-user-behavior
    (term
     (let [(counterb ,example-counter-behavior)
           (receivingb (behavior [] (fn [response] response)))
           (counter (spawn counterb 0))]
       (do
           (send counter "add" 5)
         (send counter "add" 3)
         (send counter "get" self)
         (become receivingb)))))
  (define example-counter (initial-conf (fn [] ,example-counter-user-behavior))))

; Reduction relation for language with actors.
(define ->a
  (reduction-relation
   La
   #:domain p
   ; Copied from base language
   ; We cannot use extend-reduction-relation as the domain looks different.
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
        "if_false")
   ; New:
   (--> (in-hole P (behavior [x ...] e))
        (in-hole P (fn [x ...] e))
        "behavior") ; behavior is syntactic sugar fn
   (--> ((a_0 ... (address_1 (in-hole E self) e_next) a_2 ...) μ)
        ((a_0 ... (address_1 (in-hole E address_1) e_next) a_2 ...) μ)
        "self")
   (--> ((a_0 ... (address_1 (in-hole E (become v_behavior v_0 ...)) e_next) a_2 ...) μ)
        ((a_0 ... (address_1 (in-hole E nil) (v_behavior v_0 ...)) a_2 ...) μ)
        (side-condition (not (eq? (term v_behavior) (term same))))
        "become")
   (--> ((a_0 ... (address_1 (in-hole E (become same v_0 ...)) (v_old v_old1 ...)) a_2 ...) μ)
        ((a_0 ... (address_1 (in-hole E nil) (v_old v_0 ...)) a_2 ...) μ)
        "become_same")
   (--> ((a_0 ... (address_1 (in-hole E (spawn v_behavior v_0 ...)) e_next) a_2 ...)
         (inbox_0 ...))
        ((a_0 ... (address_1 (in-hole E address_new) e_next) (address_new (v_behavior v_0 ...) (v_behavior v_0 ...)) a_2 ...)
         (inbox_0 ... (address_new ())))
        (fresh address_new)
        "spawn")
   (--> ((a_0 ... (address_1 (in-hole E (send address_to v_0 ...)) e_next) a_2 ...)
         (inbox_0 ... (address_to (m_1 ...)) inbox_2 ...))
        ((a_0 ... (address_1 (in-hole E nil) e_next) a_2 ...)
         (inbox_0 ... (address_to (m_1 ... (address_1 address_to (v_0 ...)))) inbox_2 ...))
        "send")
   (--> ((a_0 ... (address_1 (in-hole E (receive e_fn)) e_next) a_2 ...)
         (inbox_0 ... (address_1 ((address_sender address_1 (v_0 ...)) m_1 ...)) inbox_2 ...))
        ((a_0 ... (address_1 (in-hole E (e_fn v_0 ...)) e_next) a_2 ...)
         (inbox_0 ... (address_1 (m_1 ...)) inbox_2 ...))
        "receive")
   (--> ((a_0 ... (address_1 v e_next) a_2 ...) μ)
        ((a_0 ... (address_1 (receive e_next) e_next) a_2 ...) μ)
        "end of turn")))

(module+ test
  ; Returns true if lists `l1` and `l2` contain the same elements.
  (define (same-elements? l1 l2)
    (set=? (list->set l1) (list->set l2)))

  ; Final configuration of the program when there's only one actor that always
  ; keeps the same behavior.
  (define-syntax-rule (final-conf e)
    (term (((address_0
             (receive (fn [] ,e))
             (fn [] ,e)))
           ((address_0 ())))))
  
  ; Test ->a
  ; Examples from base language
  #;(traces ->a (initial-conf (fn [] ,example-sum)))
  (test-->> ->a (initial-conf (fn [] ,example-sum))
            (final-conf example-sum))
  #;(traces ->a (initial-conf (fn [] ,example-doubling)))
  (test-->> ->a (initial-conf (fn [] ,example-doubling))
            (final-conf example-doubling))
  (test-->> ->a (initial-conf (fn [] ,example-sum-3))
            (final-conf example-sum-3))
  (test-->> ->a (initial-conf (fn [] ,example-base-language))
            (final-conf example-base-language))

  #;(traces ->a example-become)
  (test-->> ->a
            ;#:equiv same-elements?
            example-become
            (term (((address_0
                     (receive ((fn [y] (fn [] 7)) 5))
                     ((fn [y] (fn [] 7)) 5)))
                   ((address_0 ())))))
  #;(traces ->a example-spawn)
  (test-->> ->a
            ;#:equiv same-elements?
            example-spawn
            (term (((address_0
                     (receive (fn [] ,example-spawn-behavior))
                     (fn [] ,example-spawn-behavior))
                    (address_new
                     (receive ((fn [] (fn [] 7))))
                     ((fn [] (fn [] 7)))))
                   ((address_0 ())
                    (address_new ())))))
  #;(traces ->a example-send)
  (test-->> ->a
            ;#:equiv same-elements?
            example-send
            (term (((address_0
                     (receive (fn [] ,example-send-behavior))
                     (fn [] ,example-send-behavior))
                    (address_new
                     (receive ((fn [] (fn [x] x))))
                     ((fn [] (fn [x] x)))))
                   ((address_0 ()) (address_new ())))))
  #;(traces ->a example-counter) ; => 191 terms
  ; The test below does not seem to terminate in a reasonable amount of time?
  ; However, the traces above work and reduce to the correct value.
  #;(test-->> ->a
            ;#:equiv same-elements?
            example-counter
            (term (((address_0
                     (receive ((fn [] (fn [response] response))))
                     (((fn [] (fn [response] response)))))
                    (address_new
                     ((fn [arg1 arg2]
                          (if (= arg1 "add")
                              (become same (+ 8 arg2))
                              (if (= arg1 "get")
                                  (send arg2 8)
                                  false)))
                      8)
                     ((fn [i]
                          (fn [arg1 arg2]
                              (if (= arg1 "add")
                                  (become same (+ 8 arg2))
                                  (if (= arg1 "get")
                                      (send arg2 8)
                                      false))))
                      8)))
                   ((address_0 ()) (address_new ()))))))

(module+ test
  (test-results))
