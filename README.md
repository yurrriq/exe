Exe Prover
==========

Depentent Records and Inductive Constructions
---------------------------------------------

This research project dedicated to formalization and implementation of Exe functional
language with dependent-types that compiles to untyped Erlang AST that can be compiler
with regular Erlang `erlc` compiler and run under BEAM or LING virtual machines.

<center><img src="http://5ht.co/exe.svg" width="600"></center>

This labguage relies on pure Calculus of Construction with 1 axiom and four deduction rules,
inductive `data` and coinductive `record` dependent definitions, and also impredicative
indexed universums. Pure CoC and impredicative universums are included into the core of
the language -- Om, with reduced Exe syntax, that is able typecheck and normilize terms.

Fearures
--------

* inductive `data` and coinductive `record` dependent constructions (Exe)
* case (pattern-matching Exe)
* receive, send, spawn (process-calculus core Exe)
* Pi, lambda, variables (core Om language)
* typechecking and normalization (Om)
* no recursion in lambdas
* recursive type definitions only
* compact base library with dependent types (Exe)
* theorems for base library (Lean)
* Erlang AST generation

Credits
-------

* Maxim Sokhatsky
* Pavel Lutko
