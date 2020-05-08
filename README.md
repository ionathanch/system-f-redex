# System F in Redex

This is an implementation of a Church-style (explicitly typed-annotated) System F (polymorphic) lambda calculus with definitions (let-expressions) in Redex. Included are:

### System F
* Type synthesis, term evaluation
* Church encodings of numerals and arithmetic (in progress)

### ANF-Restricted System F
* Type synthesis, term evaluation 
* Continuation-plugging
* Compiler from System F to ANF-restricted System F

### (ANF-Restricted) System F with Closures
* Type synthesis, term evaluation
* Compiler from ANF-restricted System F to closure-converted System F

### System Fω (extends System F)
* Why? I don't know.
* Type synthesis, term evaluation, type evaluation

### `redex-chk`, but Better
* Renames `judgment` to `judgement`
* Adds `redex-judgement-equals-chk` to test for equivalence between judgement output term and a provided term

### Reduction Strategies
* This doesn't belong here

## TODOs
* Implement hoisting pass!
* Fix ambiguity of ANF let-evaluation context
* Add evaluation context for call-by-name, normal order evaluation (why? CBN doesn't follow the "intuitive" notion of how a program runs)
* Finish Church encodings (F)
* Add inventory of metafunctions and how to run things to this README
* Fix `redex-judgement-equals-chk` macro so that when check-true fails, the highlight goes over the failed branch, not over the macro itself (redex-chk)

