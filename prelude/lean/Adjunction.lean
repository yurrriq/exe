/- Adjunction -/

import Setoid
import Cat
import Mor
import Functor

namespace Adj

    abbreviation TriangleLProp {C D : CatType} (L : D⟶C) (R : C⟶D)
        (η : 𝟙 ⟹ (R ⊗ L)) (ε : (L ⊗ R) ⟹ 𝟙) : Prop
    := ∀ (X : D), ((ε /$$ (L $$ X)) ⊙C⊙ (L $$/ (η /$$ X))) ≡((L X) ⇒C⇒ (L X))≡ ①

    abbreviation TriangleRProp {C D : CatType} (L : D⟶C) (R : C⟶D)
        (η : 𝟙 ⟹ (R ⊗ L)) (ε : (L ⊗ R) ⟹ 𝟙) : Prop
    := ∀ (Y : C), ((R $$/ (ε /$$ Y)) ⊙D⊙ (η /$$ (R $$ Y))) ≡((R Y) ⇒D⇒ (R Y))≡ ①

end Adj

record AdjType {C D : CatType} (L : D⟶C) (R : C⟶D) : Type :=
    (unit : 𝟙 ⟹ (R ⊗ L) )
    (counit : (L ⊗ R) ⟹ 𝟙 )
    (triangleL : Adj.TriangleLProp L R unit counit)
    (triangleR : Adj.TriangleRProp L R unit counit)

infix `⊣`:10 := AdjType

record LeftAdj {C D : CatType} (Right : C⟶D) : Type := (Left : D ⟶ C) (adj : Left ⊣ Right)
record RightAdj {C D : CatType} (Left : D ⟶ C) : Type := (Right : C⟶D) (adj : Left ⊣ Right)

definition Lim (C D : CatType) := RightAdj (Cat.Delta C D)
definition HaveAllLim (D : CatType) : Type := Π (C : CatType), Lim C D
record CompleteCatType : Type := (C : CatType) (Lim : HaveAllLim C)

definition Colim (C D : CatType) := LeftAdj (Cat.Delta C D)
definition HaveAllColim (D : CatType) : Type := Π (C : CatType), Colim C D
record CocompleteCatType : Type := (C : CatType) (Colim : HaveAllColim C)

namespace Adjunction
namespace IsoOnLR

    definition LtoR
        {C D : CatType} {L : D⟶C} {R : C⟶D}
        (adj : AdjType L R) (X : D) (Y : C)
        : (L X ⇒C⇒ Y) ⥤ (X ⇒D⇒ R Y)
    := let ε := AdjType.counit adj, η := AdjType.unit adj in Setoid.MkHom
            ( λ (f : L X ⇒C⇒ Y), (R $$/ f) ⊙D⊙ (η /$$ X))
            ( λ (f1 f2 : L X ⇒C⇒ Y), λ (eq : f1 ≡(L X ⇒C⇒ Y)≡ f2), (R $$// eq) /⊙D⊙ (η /$$ X))

    definition RtoL
        {C D : CatType} {L : D⟶C} {R : C⟶D}
        (adj : AdjType L R) (X : D) (Y : C)
        : (X ⇒D⇒ R Y) ⥤ (L X ⇒C⇒ Y)
    := let ε := AdjType.counit adj, η := AdjType.unit adj in Setoid.MkHom
            ( λ (g : X ⇒D⇒ R Y), (ε /$$ Y) ⊙C⊙ (L $$/ g))
            ( λ (g1 g2 : X ⇒D⇒ R Y), λ (eq : g1 ≡(X ⇒D⇒ R Y)≡ g2), (ε /$$ Y) ⊙C⊙/ (L $$// eq))

    definition LeqL
        {C D : CatType} {L : D⟶C} {R : C⟶D}
        (adj : AdjType L R) (X : D) (Y : C) (f : L X ⇒C⇒ Y)
        : let ε := AdjType.counit adj, η := AdjType.unit adj in
            ((ε /$$ Y) ⊙C⊙ (L $$/ ((R $$/ f) ⊙D⊙ (η /$$ X)))) ≡(L X ⇒C⇒ Y)≡ f
    := let ε := AdjType.counit adj, η := AdjType.unit adj in
            begin
            refine (CatType.MulHE C (ε /$$ Y) (FunctorType.onMul L (R $$/ f) (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡ _,
            refine (CatType.AssocInv C (ε /$$ Y) (L $$/ (R $$/ f)) (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡ _,
            refine (CatType.MulEH C (ε /$$/ f) (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡ _,
            refine (CatType.Assoc C f (ε /$$ (L $$ X)) (L $$/ (η /$$ X))) ⊡(L X ⇒C⇒ Y)⊡ _,
            refine (CatType.MulHE C f (AdjType.triangleL adj X)) ⊡(L X ⇒C⇒ Y)⊡ _,
            refine (CatType.UnitR C f)
            end

    definition ReqR
        {C D : CatType} {L : D⟶C} {R : C⟶D}
        (adj : AdjType L R) (X : D) (Y : C) (g : X ⇒D⇒ R Y)
        : let ε := AdjType.counit adj, η := AdjType.unit adj in
            ((R $$/ ((ε /$$ Y) ⊙C⊙ (L $$/ g))) ⊙D⊙ (η /$$ X)) ≡(X ⇒D⇒ R Y)≡ g
    := let ε := AdjType.counit adj, η := AdjType.unit adj in
            sorry

end IsoOnLR

    definition IsoOnLR
        {C D : CatType} {L : D⟶C} {R : C⟶D}
        (adj : AdjType L R) (X : D) (Y : C)
        : (L X ⇒C⇒ Y) ⇔ (X ⇒D⇒ R Y)
    :=
        CatType.MkIso
            (@IsoOnLR.LtoR C D L R adj X Y)
            (@IsoOnLR.RtoL C D L R adj X Y)
            (@IsoOnLR.LeqL C D L R adj X Y)
            (@IsoOnLR.ReqR C D L R adj X Y)

end Adjunction
