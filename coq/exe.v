
Require Import Lists.Streams.
Require Import ZArith.
Import Streams.
Import ZArith.

  CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
    let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).
  
  