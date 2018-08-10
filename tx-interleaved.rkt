#lang racket

(require redex)
(require "set.rkt")
(require "map.rkt")
(require "actors.rkt")
(require (only-in "clj-base.rkt" subst))

(provide Lt ->t)

(module+ test
  (require (submod "clj-base.rkt" test))
  (require (submod "actors.rkt" test))
  (provide (all-defined-out)))

; Language with transactions, extends actor language.
(define-extended-language Lt La
  ; transactional variable
  (r ::= variable-not-otherwise-mentioned)
  ; transaction id
  (tid ::= variable-not-otherwise-mentioned)
  ; transaction
  (tx ::= (tid ○ σ δ e)) ; last e = copy of contents of transaction, for retry
  (○ ::=
     ▶
     ✓
     ✗)
  ; heap
  (σ ::= ((r v) ...))
  ; local store
  (δ ::= ((r v) ...))
  ; map actor id → current tx id
  ; If no transaction is running the actor is simply not present in this map.
  ; (This is different from the semantics in LaTeX, where this information is stored in the actor itself.)
  (actor->tx ::= (actor-tx ...))
  (actor-tx ::= (address tid))

  (v ::= ....
     r)
  (e ::= ....
     (atomic e)
     (ref e)
     (deref e)
     (ref-set e e)
     (commit e)) ; not to be used by the programmer directly
  (transactions ::= (tx ...))
  (p ::= (actors transactions actor->tx μ σ))
  
  (P ::= (ACTORS transactions actor->tx μ σ))
  (E ::= ....
     (ref E)
     (deref E)
     (ref-set E e)
     (ref-set r E)
     (commit E)))

(module+ test
  ; Inject behavior `e` in the initial configuration.
  ; Initial configuration contains an (empty) message from the initial actor
  ; to itself.
  (define-syntax-rule (initial-conf e)
    (term (((address_0 nil e)) () () ((address_0 ((address_0 address_0 ())))) ())))

  ; Define examples and test whether they're in the language.
  (test-in-language? Lt (term (((address_0 (+ 1 2) (fn [] (+ 1 2)))) () () () ())))
  (test-in-language? Lt (initial-conf (fn [] ,example-doubling)))
  (test-in-language? Lt (initial-conf (fn [] ,example-become-behavior)))
  (test-in-language? Lt (initial-conf (fn [] ,example-spawn-behavior)))
  (test-in-language? Lt (initial-conf (fn [] ,example-send-behavior)))

  (define example-tx-body-one
    ; the body of a transaction, reused in different tests
    (term (ref-set a (+ (deref a) 1))))
  (define example-tx-body-two
    ; the body of a transaction, reused in different tests
    (term (do
              (ref-set a (+ (deref a) 1))
            (ref-set b (+ (deref b) 1))
            (+ (deref a) (deref b)))))
  (define example-tx-very-simple
    (initial-conf
     (fn []
         (let [(a (ref 0))]
           (atomic
            ,example-tx-body-one)))))
  (define example-tx-simple
    (initial-conf
     (fn []
         (let [(a (ref 0))
               (b (ref 1))]
           (atomic
            ,example-tx-body-two)))))
  (define example-tx-two-seq-tx
    (initial-conf
     (fn []
         (let [(a (ref 0))
               (b (ref 1))]
           (do (atomic ,example-tx-body-two)
             (atomic ,example-tx-body-two))))))
  ; This test has too many interleavings to execute in a reasonable amount of time.
  ; The one underneath tests the same but using only two actors.
  #;(define example-tx-two-par-tx
      ; determinate: order of tx's not defined, but result will always be the same
      (initial-conf
       (fn []
           (let [(a (ref 0))
                 (beh (behavior [] (fn [] (atomic ,example-tx-body-one))))
                 (one (spawn beh))
                 (two (spawn beh))]
             (do (send one)
               (send two))))))
  (define example-tx-two-par-tx
    ; determinate: order of tx's not defined, but result will always be the same
    (initial-conf
     (fn []
         (let [(a (ref 0))
               (other (spawn (behavior [] (fn [] (atomic ,example-tx-body-one)))))]
           (do (send other)
             (atomic ,example-tx-body-one))))))
  ; This test has too many interleavings to execute in a reasonable amount of time.
  ; The one underneath tests the same but using only two actors.
  #;(define example-tx-non-det
      ; non-determinate: different results possible
      (initial-conf
       (fn []
           (let [(a (ref 0))
                 (one (spawn (behavior [] (fn [] (atomic (ref-set a 1))))))
                 (two (spawn (behavior [] (fn [] (atomic (ref-set a 2))))))]
             (do (send one)
               (send two)
               (atomic (deref a)))))))
  (define example-tx-non-det
    ; non-determinate: different results possible
    (initial-conf
     (fn []
         (let [(a (ref 0))
               (other (spawn (behavior [] (fn [] (atomic (ref-set a 2))))))]
           (do (send other)
             (atomic
              (do
                  (ref-set a 1)
                (deref a))))))))

  (test-in-language? Lt example-tx-very-simple)
  (test-in-language? Lt example-tx-simple)
  (test-in-language? Lt example-tx-two-seq-tx)
  (test-in-language? Lt example-tx-two-par-tx)
  (test-in-language? Lt example-tx-non-det))

; Reduction relation for language with transactions.
; ->t_without_commit_✗ excludes the rule for a failing commit, ->t adds it to this relation.
(define ->t_without_commit_✗
  (reduction-relation
   Lt
   #:domain p
   ; Copied from actor language La
   ; We cannot use extend-reduction-relation as the domain looks different.
   ; TODO: find a better way to do this.
   ; Base language:
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
   ; Actor language:
   ; The rules that are not of the form (in-hole P ...) have been updated to reflect the new configuration.
   (--> (in-hole P (behavior [x ...] e))
        (in-hole P (fn [x ...] e))
        "behavior") ; behavior is syntactic sugar fn
   (--> ((a_0 ... (address_1 (in-hole E self) e_next) a_2 ...) transactions actor->tx μ σ)
        ((a_0 ... (address_1 (in-hole E address_1) e_next) a_2 ...) transactions actor->tx μ σ)
        "self")
   (--> ((a_0 ... (address_1 (in-hole E (become v_behavior v_0 ...)) e_next) a_2 ...) transactions actor->tx μ σ)
        ((a_0 ... (address_1 (in-hole E nil) (v_behavior v_0 ...)) a_2 ...) transactions actor->tx μ σ)
        (side-condition (not (eq? (term v_behavior) (term same))))
        "become")
   (--> ((a_0 ... (address_1 (in-hole E (become same v_0 ...)) (v_old v_old1 ...)) a_2 ...) transactions actor->tx μ σ)
        ((a_0 ... (address_1 (in-hole E nil) (v_old v_0 ...)) a_2 ...) transactions actor->tx μ σ)
        "become_same")
   (--> ((a_0 ... (address_1 (in-hole E (spawn v_behavior v_0 ...)) e_next) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ...)
         σ)
        ((a_0 ... (address_1 (in-hole E address_new) e_next) (address_new (v_behavior v_0 ...) (v_behavior v_0 ...)) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ... (address_new ()))
         σ)
        (fresh address_new)
        "spawn")
   (--> ((a_0 ... (address_1 (in-hole E (send address_to v_0 ...)) e_next) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ... (address_to (m_1 ...)) inbox_2 ...)
         σ)
        ((a_0 ... (address_1 (in-hole E nil) e_next) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ... (address_to (m_1 ... (address_1 address_to (v_0 ...)))) inbox_2 ...)
         σ)
        "send")
   (--> ((a_0 ... (address_1 (in-hole E (receive e_fn)) e_next) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ... (address_1 ((address_sender address_1 (v_0 ...)) m_1 ...)) inbox_2 ...)
         σ)
        ((a_0 ... (address_1 (in-hole E (e_fn v_0 ...)) e_next) a_2 ...)
         transactions
         actor->tx
         (inbox_0 ... (address_1 (m_1 ...)) inbox_2 ...)
         σ)
        "receive")
   (--> ((a_0 ... (address_1 v e_next) a_2 ...) transactions actor->tx μ σ)
        ((a_0 ... (address_1 (receive e_next) e_next) a_2 ...) transactions actor->tx μ σ)
        "end of turn")
   ; TODO: some of these rules could possibly be made easier using redex's "with" feature

   ; New for transactions:
   (--> ((in-hole ACTORS (ref v)) transactions actor->tx μ σ)
        ((in-hole ACTORS r_new) transactions actor->tx μ (map-set σ r_new v))
        (fresh r_new)
        "ref outside tx")
   ; TODO: ref in tx
   ; TODO: atomic in tx
   (--> ((a_0 ... (address_1 (in-hole E (atomic e)) e_next) a_2 ...)
         transactions
         ; TODO: check that no tx is running already:
         ; address_1 not present in mapping actor->tx
         actor->tx
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E (commit e)) e_next) a_2 ...)
         (set-add transactions (tid_new ▶ σ () e))
         (set-add actor->tx (address_1 tid_new))
         μ
         σ)
        (fresh tid_new)
        "atomic")
   (--> ((a_0 ... (address_1 (in-hole E (deref r)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E v) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        (where #true (map-contains? δ r))
        (where v (map-get δ r))
        "deref local")
   (--> ((a_0 ... (address_1 (in-hole E (deref r)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E v) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        (where #false (map-contains? δ r))
        (where v (map-get σ_original r))
        "deref global")
   (--> ((a_0 ... (address_1 (in-hole E (ref-set r v)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E v) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original (map-set δ r v) e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        "ref-set")
   (--> ((a_0 ... (address_1 (in-hole E (commit v)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E v) e_next) a_2 ...)
         (tx_0 ... (tid_1 ✓ σ_original δ e_original) tx_2 ...)
         ; We keep the transaction on record: in a conventional language with transactions
         ; we could remove this, but when adding transactional actors we will need this.
         (actor-tx_0 ... actor-tx_2 ...)
         μ
         σ_updated)
        ; if: ∀ r ∈ dom(δ): σ(r) = σ_original(r)
        (side-condition
         (andmap
          (λ (x->v)
            (let* ((x (car x->v))
                   (v_before (term (map-get σ_original ,x)))
                   (v_now (term (map-get σ ,x))))
              (equal? v_before v_now)))
          (term δ)))
        (where σ_updated (map-merge σ δ))
        "commit ✓")))

; Reduction relation for language with transactions, with failing commit.
(define ->t
  (extend-reduction-relation
   ->t_without_commit_✗
   Lt
   (--> ((a_0 ... (address_1 (in-hole E (commit v)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ▶ σ_original δ e_original) tx_2 ...)
         (actor-tx_0 ... (address_1 tid_1) actor-tx_2 ...)
         μ
         σ)
        ((a_0 ... (address_1 (in-hole E (atomic e_original)) e_next) a_2 ...)
         (tx_0 ... (tid_1 ✗ σ_original δ e_original) tx_2 ...)
         ; We keep the transaction on record: in a conventional language with transactions
         ; we could remove this, but when adding transactional actors we will need this.
         (actor-tx_0 ... actor-tx_2 ...)
         μ
         σ)
        ; if: ∃ r ∈ dom(δ): σ(r) ≠ σ_original(r)
        ; = not(∀ r ∈ dom(δ): σ(r) = σ_original(r))
        (side-condition
         (not
          (andmap
           (λ (x->v)
             (let* ((x (car x->v))
                    (v_before (term (map-get σ_original ,x)))
                    (v_now (term (map-get σ ,x))))
               (equal? v_before v_now)))
           (term δ))))
        (where σ_updated (map-merge σ δ))
        "commit ✗")))

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
           ()
           ()
           ((address_0 ()))
           ())))
  
  ; Test ->t
  ; Examples from base language
  #;(traces ->t (initial-conf (fn [] ,example-sum)))
  (test-->> ->t (initial-conf (fn [] ,example-sum))
            (final-conf example-sum))
  #;(traces ->t (initial-conf (fn [] ,example-doubling)))
  (test-->> ->t (initial-conf (fn [] ,example-doubling))
            (final-conf example-doubling))
  (test-->> ->t (initial-conf (fn [] ,example-sum-3))
            (final-conf example-sum-3))
  (test-->> ->t (initial-conf (fn [] ,example-base-language))
            (final-conf example-base-language))

  (define example-tx-body-one-renamed-variables
    (term (ref-set r_new (+ (deref r_new) 1))))

  (define example-tx-body-two-renamed-variables
    (term (do (ref-set r_new (+ (deref r_new) 1))
            (ref-set r_new1 (+ (deref r_new1) 1))
            (+ (deref r_new) (deref r_new1)))))
  
  #;(traces ->t example-tx-very-simple)
  (test-->> ->t
            example-tx-very-simple
            (term (((address_0
                     (receive
                      (fn []
                          (let [(a (ref 0))]
                            (atomic ,example-tx-body-one))))
                     (fn []
                         (let [(a (ref 0))]
                           (atomic ,example-tx-body-one)))))
                   ((tid_new
                     ✓
                     ((r_new 0))
                     ((r_new 1))
                     ,example-tx-body-one-renamed-variables))
                   ()
                   ((address_0 ()))
                   ((r_new 1) (r_new 0)))))
  #;(traces ->t example-tx-simple)
  (test-->> ->t
            example-tx-simple
            (term (((address_0
                     (receive
                      (fn []
                          (let [(a (ref 0))
                                (b (ref 1))]
                            (atomic ,example-tx-body-two))))
                     (fn []
                         (let [(a (ref 0))
                               (b (ref 1))]
                           (atomic ,example-tx-body-two)))))
                   ((tid_new
                     ✓
                     ((r_new1 1) (r_new 0))
                     ((r_new1 2) (r_new 1))
                     ,example-tx-body-two-renamed-variables))
                   ()
                   ((address_0 ()))
                   ((r_new1 2) (r_new 1) (r_new1 1) (r_new 0)))))
  #;(traces ->t example-tx-two-seq-tx)
  (test-->> ->t
            example-tx-two-seq-tx
            (term (((address_0
                     (receive
                      (fn []
                          (let [(a (ref 0))
                                (b (ref 1))]
                            (do (atomic ,example-tx-body-two)
                              (atomic ,example-tx-body-two)))))
                     (fn []
                         (let [(a (ref 0))
                               (b (ref 1))]
                           (do (atomic ,example-tx-body-two)
                             (atomic ,example-tx-body-two))))))
                   ((tid_new
                     ✓
                     ((r_new1 1) (r_new 0))
                     ((r_new1 2) (r_new 1))
                     ,example-tx-body-two-renamed-variables)
                    (tid_new1
                     ✓
                     ((r_new1 2) (r_new 1) (r_new1 1) (r_new 0))
                     ((r_new1 3) (r_new 2))
                     ,example-tx-body-two-renamed-variables))
                   ()
                   ((address_0 ()))
                   ((r_new1 3) (r_new 2) (r_new1 2) (r_new 1) (r_new1 1) (r_new 0)))))

  ; There are two schedules: tx 1 executes first or tx 2 first.
  ; The end result is the same for this program though.
  #;(traces ->t_without_commit_✗ example-tx-two-par-tx) ; 173 terms
  ; Note: we use ->t_without_commit_✗, because ->t leads to an infinite graph as transactions can
  ; conflict and retry over and over.
  ; When using ->t_without_commit_✗, next to the successful end result below, there are a others
  ; that correspond to executions that lead to conflicts. That is why we use test-->>∃ and not test-->>.
  (test-->>∃ ->t_without_commit_✗
             example-tx-two-par-tx
             (term (((address_0
                      (receive
                       (fn ()
                           (let ((a (ref 0))
                                 (other (spawn (behavior () (fn () (atomic (ref-set a (+ (deref a) 1))))))))
                             (do (send other)
                               (atomic (ref-set a (+ (deref a) 1)))))))
                      (fn ()
                          (let ((a (ref 0))
                                (other (spawn (behavior () (fn () (atomic (ref-set a (+ (deref a) 1))))))))
                            (do (send other)
                              (atomic (ref-set a (+ (deref a) 1)))))))
                     (address_new
                      (receive
                       ((fn () (fn () (atomic (ref-set r_new (+ (deref r_new) 1)))))))
                      ((fn () (fn () (atomic (ref-set r_new (+ (deref r_new) 1))))))))
                    ((tid_new
                      ✓
                      ((r_new 0))
                      ((r_new 1))
                      (ref-set r_new (+ (deref r_new) 1)))
                     (tid_new1
                      ✓
                      ((r_new 1) (r_new 0))
                      ((r_new 2))
                      (ref-set r_new (+ (deref r_new) 1))))
                    ()
                    ((address_0 ()) (address_new ()))
                    ((r_new 2) (r_new 1) (r_new 0)))))

  ; There are two schedules: tx 1 executes first or tx 2 first.
  ; The end result is the different:
  ; if tx 1 executes first, followed by tx 2, the final value of a is 2;
  ; if tx 2 executes first, followed by tx 1, the final value of a is 1.
  #;(traces ->t_without_commit_✗ example-tx-non-det) ; 138 terms
  ; Note: we use ->t_without_commit_✗, because ->t leads to an infinite graph as transactions can
  ; conflict and retry over and over.
  ; When using ->t_without_commit_✗, next to the successful end result below, there are a others
  ; that correspond to executions that lead to conflicts. That is why we use test-->>∃ and not test-->>.
  (test-->>∃ ->t_without_commit_✗
             example-tx-non-det
             (term (((address_0
                      (receive
                       (fn ()
                           (let ((a (ref 0))
                                 (other (spawn (behavior () (fn () (atomic (ref-set a 2)))))))
                             (do (send other)
                               (atomic (do (ref-set a 1) (deref a)))))))
                      (fn ()
                          (let ((a (ref 0))
                                (other (spawn (behavior () (fn () (atomic (ref-set a 2)))))))
                            (do (send other)
                              (atomic (do (ref-set a 1) (deref a)))))))
                     (address_new
                      (receive
                       ((fn () (fn () (atomic (ref-set r_new 2))))))
                      ((fn () (fn () (atomic (ref-set r_new 2)))))))
                    ((tid_new
                      ✓
                      ((r_new 0))
                      ((r_new 1))
                      (do (ref-set r_new 1) (deref r_new)))
                     (tid_new1
                      ✓
                      ((r_new 1) (r_new 0))
                      ((r_new 2))
                      (ref-set r_new 2)))
                    ()
                    ((address_0 ()) (address_new ()))
                    ((r_new 2) (r_new 1) (r_new 0)))))
  (test-->>∃ ->t_without_commit_✗
             example-tx-non-det
             (term (((address_0
                      (receive
                       (fn ()
                           (let ((a (ref 0))
                                 (other (spawn (behavior () (fn () (atomic (ref-set a 2)))))))
                             (do (send other)
                               (atomic (do (ref-set a 1) (deref a)))))))
                      (fn
                       ()
                       (let ((a (ref 0))
                             (other (spawn (behavior () (fn () (atomic (ref-set a 2)))))))
                         (do (send other)
                           (atomic (do (ref-set a 1) (deref a)))))))
                     (address_new
                      (receive
                       ((fn () (fn () (atomic (ref-set r_new 2))))))
                      ((fn () (fn () (atomic (ref-set r_new 2)))))))
                    ((tid_new
                      ✓
                      ((r_new 0))
                      ((r_new 2))
                      (ref-set r_new 2))
                     (tid_new1
                      ✓
                      ((r_new 2) (r_new 0))
                      ((r_new 1))
                      (do (ref-set r_new 1) (deref r_new))))
                    ()
                    ((address_0 ()) (address_new ()))
                    ((r_new 1) (r_new 2) (r_new 0))))))

(module+ test
  (test-results))
