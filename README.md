Exe Language
============

Dependent Records and Inductive Constructions
---------------------------------------------

This research project is dedicated to formalization and implementation of Exe functional
language with dependent types that compiles to untyped Erlang AST that can be compiled
with regular Erlang `erlc` compiler and run under BEAM or LING virtual machines.

<center><img src="http://5ht.co/exe.svg" width="600"></center>

This language relies on pure Calculus of Construction with 1 axiom and four deduction rules,
inductive `data` and coinductive `record` dependent definitions, and also impredicative
indexed universes. Pure CoC and impredicative universes are included into the core language with reduced syntax -- [Om](https://github.com/5HT/om) -- that is able to typecheck and normalize terms.

Features
--------

* inductive `data` and coinductive `record` dependent constructions (Exe)
* Berrarducci encoding for (co)-inductive constructions (Exe)
* map inductive types to Erlang types (Exe)
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
