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

record LeftAdj {C D : CatType} (Right : C⟶D) : Type :=
    (Left : D ⟶ C)
    (adj : Left ⊣ Right)

record RightAdj {C D : CatType} (Left : D ⟶ C) : Type :=
    (Right : C⟶D)
    (adj : Left ⊣ Right)

abbreviation Lim (C D : CatType) := RightAdj (Cat.Delta C D)
abbreviation Colim (C D : CatType) := LeftAdj (Cat.Delta C D)

abbreviation HaveLimType (D : CatType) : Type := Π (C : CatType), Lim C D
abbreviation HaveColimType (D : CatType) : Type := Π (C : CatType), Colim C D

record CompleteCatType : Type :=
    (C : CatType)
    (Lim : HaveLimType C)

record CocompleteCatType : Type :=
    (C : CatType)
    (Lim : HaveColimType C)
