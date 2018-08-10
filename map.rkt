#lang racket

(require redex)
(require "clj-base.rkt")

(provide map-get map-set map-set* map-merge map-contains?)

; Looks up a key in a map.
(define-metafunction Lb
  map-get : ((any any) ...) any -> any
  [(map-get ((any_k1 any_v1) ... (any_k any_v) (any_k2 any_v2) ...) any_k)
   any_v
   (side-condition (not (member (term any_k) (term (any_k1 ...)))))]
  [(map-get any_map any_k)
   ,(error 'map-get "not found: ~e in: ~e" (term any_k) (term any_map))])

; Add binding to map.
; TODO: overwrite instead of add? This doesn't really matter
; for the semantics, but is cleaner.
(define-metafunction Lb
  map-set : ((any any) ...) any any -> ((any any) ...)
  [(map-set ((any_k any_v) ...) any_k1 any_v1)
   ((any_k1 any_v1) (any_k any_v) ...)])

; Extends map with more bindings.
; TODO: overwrite instead of add? This doesn't really matter
; for the semantics, but is cleaner.
(define-metafunction Lb
  map-set* : ((any any) ...) (any ...) (any ...) -> ((any any) ...)
  [(map-set* ((any_k any_v) ...) (any_k1 ...) (any_v1 ...))
   ((any_k1 any_v1) ... (any_k any_v) ...)])

; Merge second map onto the first.
(define-metafunction Lb
  map-merge : ((any any) ...) ((any any) ...) -> ((any any) ...)
  [(map-merge (any_1 ...) (any_2 ...))
   (any_2 ... any_1 ...)])

; Checks whether a map contains a key.
(define-metafunction Lb
  map-contains? : ((any any) ...) any -> boolean
  [(map-contains? ((any_k1 any_v1) ... (any_k any_v) (any_k2 any_v2) ...) any_k)
   #true]
  [(map-contains? any_map any_k)
   #false])

(module+ test
  (test-equal (term (map-get ((a 55) (a 0) (b 1)) a))
              (term 55))
  (test-equal (term (map-set ((a 0) (b 1)) a 55))
              (term ((a 55) (a 0) (b 1))))
  (test-equal (term (map-set* ((a 0) (b 1)) (a) (55)))
              (term ((a 55) (a 0) (b 1))))
  (test-equal (term (map-merge ((a 0) (b 1)) ((a 55) (c 33))))
              (term ((a 55) (c 33) (a 0) (b 1)))) ; XXX ugly
  (test-equal (term (map-contains? ((a 0) (b 1)) a))
              (term #true))
  (test-equal (term (map-contains? ((a 0) (b 1)) c))
              (term #false)))

(module+ test
  (test-results))
