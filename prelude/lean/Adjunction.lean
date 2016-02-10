/- Adjunction -/

import Setoid
import Cat
import Mor
import Functor

record Adjunction {C D : CatType} (L : D⟶C) (R : C⟶D) : Type :=
    (unit : 𝟙 ⟹ (R ⊗ L) )
    (counit : (L ⊗ R) ⟹ 𝟙 )
    (triangleL : ∀ (X : D),
        ((counit /$$ (L $$ X)) ⊙C⊙ (L $$/ (unit /$$ X)))
            ≡((L X) ⇒C⇒ (L X))≡
        ① )
    (triangleR : ∀ (Y : C),
        ((R $$/ (counit /$$ Y)) ⊙D⊙ (unit /$$ (R $$ Y)))
            ≡((R Y) ⇒D⇒ (R Y))≡
        ① )

infix `⊣`:10 := Adjunction

record LeftAdj {C D : CatType} (R : C⟶D) : Type :=
    (L : D ⟶ C)
    (adj : L ⊣ R)

record RightAdj {C D : CatType} (L : D ⟶ C) : Type :=
    (R : C⟶D)
    (adj : L ⊣ R)

abbreviation Limit (C D : CatType) := RightAdj (Cat.Delta C D)
abbreviation CoLimit (C D : CatType) := LeftAdj (Cat.Delta C D)
