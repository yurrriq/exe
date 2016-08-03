EXE — DepTypes Language with Encodings
======================================

This document should drop you to EXE/OM immediately. Groupoid Infinity creates
a new programming language with dependent types called EXE with small provable dependent core called OM.
OM is an implementation of Calculus of Constructions (CoC), the pure lambda calculus with dependent types.
It can be compiled (code extraction) to bytecode of Erlang virtual machines BEAM and LING.
EXE is an implementation of Calculus of Inductive Constructions (CiC) that lives on top of CoC OM model.
You may think of EXE as AST transformation of higher language (with HITs) to OM.

Why new Dependent Language?
---------------------------

**No Fixpoint and Induction in Core**. We came up with pure CoC core having predicative
and impredicative universe hierarchies and macro extensions. Other MLTT cores have additional
axioms like Fixpoint and Induction (and even more) — something we strive to escape
because it leads to the complex core. No, we don't have Fixpoint, and yes,
we implemented Induction principle in pure CoC.

**Extensible Language Design**. Encoding of inductive types is based on categorical semantic
of compilation to CoC. All other syntax constructions are inductive definitions, plugged
into the stream parser. AST of the CoC language is also defined in terms of inductive
constructions and thus allowed in the macros. The language of polynomial functors (data
and record) and core language of the process calculus (spawn, receive and send) is just
macrosystem over CoC language, its syntax extensions.

**Changeable Encodings**. In pure CoC we have only arrows, so all inductive type encodings
would be Church-encoding variations. Most extended nowadays is Church-Boehm-Berrarducci
the encoding which dedicated to inductive types. Another well known are Scott (laziness),
Parigot (laziness and constant-time iterators) and CPS (continuations) encodings.

**Proved Categorical Semantic**. There was modeled a math model (using higher-order
categorical logic) of encoding, which calculates (co)limits in a category of (co)algebras
built with given set of (de)constructors. We call such encoding in honor of Lambek lemma
that leads us to the equality of (co)initial object and (co)limit in the categories
of (co)algebras. Such encoding works with dependent types and its consistency is proved
in Lean model.

<img src="http://groupoid.co/exe.svg" width="600">

OM — Compact Core of CoC
------------------------

In repository OM you may found following parts of core:
* [Parser](https://github.com/groupoid/om/blob/master/src/om_parse.erl)
* [Typechecker](https://github.com/groupoid/om/blob/master/src/om_type.erl)
* [Eraser](https://github.com/groupoid/om/blob/master/src/om_erase.erl) (could be improved)
* [Code Extractor](https://github.com/groupoid/om/blob/master/src/om_extract.erl)


OM ships with different `modes` (spaces of types with own encodings), or `preludes`
you may find in `priv` directory. They are selectable with `om:mode("normal")`, e.g.

### General Preludes

#### [normal](https://github.com/groupoid/om/tree/master/priv/normal)

This is minimal practical prelude similar to Morte's base library of Gabriel Gonzalez.
For modeling inductive constructions we use here plain Church (or Boehm-Berrarducci if you wish),
we have here basic I/O monads: IO (free monad, for limited I/O) and IOI (free comonad,
for infinitary I/O, long-term processes). The generated code is being sewed with
Erlang effects that are passed as parameters to pure functions.

#### [new-setoids](https://github.com/groupoid/om/tree/master/priv/new-setoids)

This is an implementation of Setoid structure, that provides us Equality. However
we switched lately to more compact `poset` encoding.

#### [posets](https://github.com/groupoid/om/tree/master/priv/posets)

This is implementation of non-reflexive partial order sets which
has more compact representation than setoids for our needs.
It has only `Bool`, `Empty` and `Unit` encoded just to show the general idea.
Dependent eliminator of `Bool` you can found here https://github.com/groupoid/om/tree/master/priv/posets/Data/Bool/

Note: all these folders (modules) are encoded in plain CoC in OM repository to demonstrate 
you the basic principles how things work. Later all these should be written in EXE languages and translated to OM
automatically. You may think of OM as the low-level typed assembler of type theory.

### Paradox Preludes

[girard](https://github.com/groupoid/om/tree/master/priv/girard),
[hurkens](https://github.com/groupoid/om/tree/master/priv/hurkens),
[russell](https://github.com/groupoid/om/tree/master/priv/russell) are preludes dedicated to
demonstration of appropriate models of paradoxes which arise in type theory and show
the inconsistency of type theory with impredicative hierarhy of universes.
You also can play with it in pure CoC and its variations.

EXE — Expressive Language of CiC
--------------------------------

EXE is top level, user language with CiC semantics and minimal yet useful syntax wich is subject to change.
EXE parser is implemented as LALR-(1) grammar using Erlang's `leex` and `yecc` applications,
and translates to OM terms, each term is a file on a filesystem and folder is a module or compilation unit (BEAM files).

Technically it is useful to distinguish different layers of EXE:

* Internal Core with `record` used as structures, modules, and namespaces for the entire language.
It transparently translates to OM as Contexts (named types and terms).

* Metaprogramming Encodings layer which allows expanding macros to Internal Core. Macros are used to
encoding programming that hides implementation details of `CPS`, `Parigot` or `Church` encodings.
However, our EXE encodings are a bit different encodings with categorical semantics, proven in Lean model.

* End-user Top-level EXE Language with powerful primitives `data` and `codata` that uses underlying
encoding macros. In the future with inductive-inductive types and HITs.
Likely Top Language would be a superset of the Internal Core sharing most of the parser.

### Macrosystems

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
