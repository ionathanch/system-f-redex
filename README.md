# System F in Redex

This is an implementation of a Church-style (explicitly typed-annotated) System F (polymorphic) lambda calculus with definitions (let-expressions) and branching (booleans) in Redex. Included are:

### System F
* Type synthesis, CBV small-step semantics
* Church encodings of numerals and some arithmetic

### ANF-Restricted System F
* Type synthesis, CBV small-step semantics
* Uses Redex's `in-hole` contexts for continuations used during compilation
* Compiler from System F to ANF-restricted System F (defined with an ambient continuation)
  * The naïve version copies the continuation twice when compiling if expressions
  * The improved version is defined over System F's typing rules and avoids code copying

### (ANF-Restricted) System F with Closures
* Type synthesis, CBV small-step semantics that evaluate closures during application
* Compiler from ANF-restricted System F to closure-converted System F (defined over System F-ANF's typing rules)

### (ANF-Restricted) Hoisted System F (with Closures)
* Type synthesis, CBV big-step semantics (implemented as a judgement rather than a reduction-relation)
* Compiler from closure-converted System F to hoisted System F
* N.B. Each code block label is only visible in subsequent code blocks

### System Fω (extends System F)
* Why? I don't know.
* Higher-kinded polymorphic lambda calculus with NO let-expressions
* Type synthesis, term evaluation, type evaluation

### `redex-chk`, but Better
* Renames `judgment` to `judgement`
* Adds `redex-judgement-equals-chk` to test for equivalence between judgement output term and a provided term

### Reduction Strategies
* This doesn't belong here

## TODOs
* Consider adding fixpoints (this might be of interest for ACC... or not)
* Add inventory of metafunctions and how to run things to this README
* Fix `redex-judgement-equals-chk` macro so that when check-true fails, the highlight goes over the failed branch, not over the macro itself (redex-chk)
* Consider a heap allocation pass. This is primarily to concretize what a closure would look like at low level. I'm guessing the free types and terms would each be an array.

