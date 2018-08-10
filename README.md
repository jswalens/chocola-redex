# PLT Redex implementation of Chocola

This repository contains a machine-executable implementation of parts of the operational semantics of [Chocola][chocola], using [PLT Redex][plt-redex].

[chocola]: http://soft.vub.ac.be/~jswalens/chocola/
[plt-redex]: https://redex.racket-lang.org/

It consists of the following files:
* `clj-base.rkt` defines Lb, the "base" language (based on Clojure)
* `futures.rkt` defines Lf, extending the base language with support for futures (as in Clojure)
* `actors.rkt` defines La, extending the base language with support for actors
* `tx-atomic.rkt` defines Lt, extending Lf with support for transactions (as in Clojure). Transactions execute in a single step, so they are trivially serializable.
* `tx-interleaved.rkt` defines another Lt, extending La with support for transactions. Transactions execute in multiple steps, so they can be interleaved.
* `tx-futs.rkt` defines Ltf, extending Lt with support for transactional futures
* `map.rkt`: helper functions for maps
* `set.rkt`: helper functions for sets

Each of the files also contains test cases. (The tests that have been commented out take a long time to execute but should succeed.)

For instance, `tx-futs.rkt` contains the following test case (named `example-tx-futs-3`):

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
      (+ (join f_0) (join f_1)))

There are two possible outcomes of this program:

    (term [[(f_0 8) (f_new1 6) (f_new 2)]
           [(r_new 6) (r_new 5) (r_new 2) (r_new 1) (r_new 0)]])
    (term [[(f_0 10) (f_new1 4) (f_new 6)]
           [(r_new 6) (r_new 5) (r_new 4) (r_new 3) (r_new 0)]])

These correspond to the two possible serializations: the first corresponds to transaction 1 executing first (end result is 8), the second to transaction 2 executing first (end result is 10).

These results can be visualized using:

    (traces ->tf example-tx-futs-3)

This is shown in the image in `example-tx-futs-3.pdf`. You can see how different interleavings lead to different intermediate states, but they collapse into two final states, corresponding to the two possible serializations.
