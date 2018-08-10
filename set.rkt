#lang racket

(require redex)
(require "clj-base.rkt")

(provide set-add set-union set-contains? set-subset?)

; Adds element to set.
(define-metafunction Lb
  set-add : (any ...) any -> (any ...)
  [(set-add (any_0 ...) any_1)
   (any_0 ... any_1)])

; Takes the union of two sets.
(define-metafunction Lb
  set-union : (any ...) (any ...) -> (any ...)
  [(set-union (any_0 ...) (any_1 ...))
   (any_0 ... any_1 ...)])

; Checks whether an element is member of a set.
(define-metafunction Lb
  set-contains? : any (any ...) -> boolean
  [(set-contains? any_x (any_0 ... any_x any_1 ...))
   #true]
  [(set-contains? any_x any_list)
   #false])

; Checks whether one set is a subset of another.
(define-metafunction Lb
  set-subset? : (any ...) (any ...) -> boolean
  [(set-subset? () any)
   #true]
  [(set-subset? (any_0 any_1 ...) (any_2 ... any_0 any_3 ...))
   (set-subset? (any_1 ...) (any_2 ... any_0 any_3 ...))]
  [(set-subset? (any_0 any_1 ...) any)
   #false])

(module+ test
  (test-equal (term (set-add (a b c) d))
              (term (a b c d)))
  (test-equal (term (set-union (a b c) (d e)))
              (term (a b c d e)))
  (test-equal (term (set-contains? a (a b c)))
              (term #true))
  (test-equal (term (set-contains? b (a b c)))
              (term #true))
  (test-equal (term (set-contains? c (a b c)))
              (term #true))
  (test-equal (term (set-contains? d (a b c)))
              (term #false))
  (test-equal (term (set-subset? (a b) (a c b))) #t)
  (test-equal (term (set-subset? (a d) (a c b))) #f))

(module+ test
  (test-results))
