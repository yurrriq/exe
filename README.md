EXE Language with Dependent Types
=================================

This document should drop you to EXE/OM immediately. Groupoid Infinity creates
a new programming language with dependent types called EXE with small provable dependent core called OM.
OM is an implementation of Calculus of Constructions (CoC), the pure lambda calculus with dependent types.
It can be compiled (code extraction) to bytecode of Erlang virtual machines BEAM and LING.
EXE is an implementation of Calculus of Inductive Constructions (CiC) that lives on top of CoC OM model.
You may think of EXE as operational transformation of higher language (with HITs) to OM.

![](http://5ht.co/exe.svg =600)

OM — Compact Core of CoC
------------------------

In repository OM you may found following parts of OM:
* Parser https://github.com/groupoid/om/blob/master/src/om_parse.erl
* Typechecker https://github.com/groupoid/om/blob/master/src/om_type.erl
* Eraser https://github.com/groupoid/om/blob/master/src/om_erase.erl
* Code Extractor https://github.com/groupoid/om/blob/master/src/om_extract.erl
Also code erasor should be improved.

OM ships with different `modes` (spaces of types with own encodings), or `preludes`
you may found in `priv` directory. We swith with `om:mode("normal")` for example.

### General Preludes

#### [normal](https://github.com/groupoid/om/tree/master/priv/normal)

This is minimal practical preludude similar to Morte's base library of Gabriel Gonzalez.
For modeling inductive constructions we use here plain Church (or Boem-Berrarducci if you wish),
we have here basic I/O monads: IO (free monad, for limited I/O) and IOI (free comonad,
for infinitary I/O, long term processes). The generated code is being sewed with
Erlang effects that are passed as parameters to pure functions.

#### [new-setoids](https://github.com/groupoid/om/tree/master/priv/new-setoids)

This is implementation of Setoid structure, that provides us Equality. However
we switched lately to more compact `poset` encoding.

#### [posets](https://github.com/groupoid/om/tree/master/priv/posets)

This is implementation of non-reflexive partial order sets which
has more compact representation than setoids for our needs.
It has only `Bool`, `Empty` and `Unit` encoded just to show general idea.
Dependent eliminator of `Bool` you can found here https://github.com/groupoid/om/tree/master/priv/posets/Data/Bool/

Note: all these folders (modules) are encoded in plain CoC in OM repository to demonstrate 
you the basic principles how things works. Later all these should be written in EXE languages and translated to OM
automatically. You may think of OM as low level typed assembler of type theory.

#### Paradox Preludes

[girard](https://github.com/groupoid/om/tree/master/priv/girard),
[hurkens](https://github.com/groupoid/om/tree/master/priv/hurkens),
[russell](https://github.com/groupoid/om/tree/master/priv/russell) are preludes dedicated to
demonstration of appropriate models of paradoxes which arise in type theory and show
the inconsistency of type theory with impredicative hierarhy of universes.
You also can play with it in pure CoC and its variations.

EXE — Expressive Language of CiC
--------------------------------

EXE is top level, user language with CiC semantics and minimal yet usefull syntax wich is subject to change.
EXE parser is implemented as LALR-(1) grammar using Erlang's `leex` and `yecc` applications,
and translates to OM terms, each term is a file on a filesystem and folder is a module or compilation unit (BEAM files).

Technically it is useful to destinguish different layers of EXE:

* Internal Core with `record` used as structures, modules and namespaces for the entire language.
It transparently translates to OM as Contexts (named types and terms).

* Metaprogramming Encodings layer which allows to expand macroses to Internal Core. Macros are used to
encoding programming that hides implementation details of `CPS`, `Parigot` or `Church` encodings.
However our EXE encodings are a bit different encodings with categorical semantics, proven in Lean model.

* End-user Top-level EXE Language with powerful primitives `data` and `codata` that uses underlying
encoding macros. In the future with inductive-inductive types and HITs.
Likely Top Language would be a superset of the Internal Core sharing most of the parser.

### EXE macros

#### [macro.new](https://github.com/groupoid/exe/blob/master/prelude/macro.new)

Proptypes of general macros built using `poset` approach. Here you can find different encodings
for basic types
[Nat](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.Nat.macro),
[Bool](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.Bool.macro),
[List](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.List.macro),
[Prod](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.Prod.macro),
[Sum](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.Sum.macro) along with
[packing macros](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.Pack.macro)
and even [Free Monad](https://github.com/groupoid/exe/blob/master/prelude/macro.new/Data.FreeMonad.macro).

#### [smart-simpleton](https://github.com/groupoid/exe/blob/master/prelude/smart-simpleton)

Most compact, final model of encodings with recursor and induction, the result of all theoretical EXE findings.

OM A HUM
