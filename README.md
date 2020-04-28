# System F in Redex

This is an implementation of a Church-style (explicitly typed-annotated) System F (polymorphic) lambda calculus with definitions (let-expressions) in Redex. Included are:

### System F
* Type synthesis
* Head normal form reduction and normal form reduction (both call-by-value)
* Church encodings of numerals and arithmetic (in progress)

### ANF-Restricted System F
* Type synthesis
* Head normal form and normal form reduction
* Continuation-plugging
* Compiler from System F to ANF-restricted System F

### Closure-Converted System F
* Under construction
* Type synthesis and reduction
* Compiler from ANF-restricted System F to closure-converted System F (not yet)

### System Fω (extends System F)
* Why? I don't know.
* Type synthesis
* Head normal form, normal form, and type-level reduction

### `redex-chk`, but Better
* Renames `judgment` to `judgement`
* Adds `redex-judgement-equals-chk` to test for equivalence between judgement output term and a provided term

## TODOs
* Add tests for ANF translation (type-preservation and correctness)
* Add tests for F-ACC reduction
* Implement abstract closure conversion from F-ANF to F-ACC
* Fix ambiguity of ANF let-evaluation context
* Add evaluation context for call-by-name evaluation (all)
* Finish Church encodings (F)
* Add inventory of metafunctions and how to run things to this README
* Fix `redex-judgement-equals-chk` macro so that when check-true fails, the highlight goes over the failed branch, not over the macro itself (redex-chk)
