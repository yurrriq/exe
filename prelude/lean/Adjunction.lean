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

abbreviation HaveAllLim (D : CatType) : Type := Π (C : CatType), Lim C D
abbreviation HaveAllColim (D : CatType) : Type := Π (C : CatType), Colim C D

record CompleteCatType : Type :=
    (C : CatType)
    (Lim : HaveAllLim C)

record CocompleteCatType : Type :=
    (C : CatType)
    (Colim : HaveAllColim C)

definition Adjunction.HomIsoLR {C D : CatType} {L : D⟶C} {R : C⟶D}
    (adj : Adjunction L R) (X : D) (Y : C) : (L X ⇒C⇒ Y) ⇔ (X ⇒D⇒ R Y)
:=
    let ε := Adjunction.counit adj, η := Adjunction.unit adj in
    CatType.MkIso
        (Setoid.MkHom -- (L X ⇒C⇒ Y) ⥤ (X ⇒D⇒ R Y)
            ( λ (f : L X ⇒C⇒ Y), (R $$/ f) ⊙D⊙ (η /$$ X))
            ( λ (f1 f2 : L X ⇒C⇒ Y), λ (eq : f1 ≡(L X ⇒C⇒ Y)≡ f2),
                eq_and_hom D (R $$// eq) (η /$$ X) ) )
        (Setoid.MkHom -- (X ⇒D⇒ R Y) ⥤ (L X ⇒C⇒ Y)
            ( λ (g : X ⇒D⇒ R Y), (ε /$$ Y) ⊙C⊙ (L $$/ g))
            ( λ (g1 g2 : X ⇒D⇒ R Y), λ (eq : g1 ≡(X ⇒D⇒ R Y)≡ g2),
                hom_and_eq C (ε /$$ Y) (L $$// eq) ) )
        ( λ (f : L X ⇒C⇒ Y),
            let
                sq : Mor.SquareProp C ((L⊗R) $$/ f) (𝟙 $$/ f) (ε /$$ (L $$ X)) (ε /$$ Y) := ε /$$/ f,
                sqq :
                    ((Adjunction.counit adj/$$Y)⊙C⊙(L$$/(R$$/f))) ≡ (L X ⇒C⇒ Y)≡
                    ((𝟙$$/f)⊙C⊙(Adjunction.counit adj/$$(L$$X))) := sorry
            in
            (hom_and_eq C (ε /$$ Y) (FunctorType.onMul L (R $$/ f) (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡
            (CatType.AssocInv C (ε /$$ Y) (L $$/ (R $$/ f)) (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡
            (eq_and_hom C sqq (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡
            (CatType.Assoc C f (ε /$$ (L $$ X)) (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡
            (hom_and_eq C f (Adjunction.triangleL adj X)) ⊡(L X ⇒C⇒ Y)⊡
            (CatType.UnitR C f) )
        sorry
