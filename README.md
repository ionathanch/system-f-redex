# System F in Redex

This is an implementation of a Church-style (explicitly typed-annotated) System F (polymorphic) lambda calculus with definitions (let-expression) in Redex. Included are:

* Various metafunctions for multi-parameter functions, multi-argument applications, multi-variable foralls, multi-type function types, and multi-entry type and term contexts
* Type inference
* Head normal form reduction and normal form reduction (both call-by-value)
* Church encodings of numerals and arithmetic (in progress)

## TODOs
* Add ANF-restricted System F (syntax, semantics if needed)
* Implement compiler from System F to ANF-restricted System F (possibly as metafunction?)
* Can you prove compiler correctness in Redex??
* Add evaluation context for call-by-name evaluation
* Finish Church encodings
* Further goal: abstract closure conversion for (ANF-restricted) System F??
  - I suspect that the annotations in F-to-TAL are only needed for parametric closure conversion, and abstract closure conversion could be done without them
