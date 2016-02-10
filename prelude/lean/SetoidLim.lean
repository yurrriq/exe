/- SetoidLim -/

import Setoid
import Mor
import Functor

/-
 - Definition of LIMIT in SetoidCat
 -/

namespace Setoid
    record LimType {C : CatType} (F : C⟶SetoidCat) : Type :=
        (atOb : Π(X : C), [F X])
        (atHom : ∀{X Y : C}, ∀(m : X ⇒C⇒ Y), (atOb Y) ≡(F Y)≡ ((F m) $ (atOb X)))
    abbreviation MkLim {C : CatType} {F : C⟶SetoidCat} := @LimType.mk C F
end Setoid

-- action
attribute Setoid.LimType.atOb [coercion]
attribute Setoid.LimType.atHom [coercion]

namespace Setoid
    definition LimSet {C : CatType} (F : C⟶SetoidCat) : SetoidType :=
        Setoid.MkOb
        (LimType F)
        ( λ(a b : LimType F), ∀(X : C), (a X) ≡(F X)≡ (b X))
        ( λ(a : LimType F), λ(X : C),
            @SetoidType.Refl (F X) (a X))
        ( λ(a b c : LimType F), λ ab bc, λ(X : C),
            @SetoidType.Trans (F X) (a X) (b X) (c X) (ab X) (bc X))
        ( λ(a b : LimType F), λ ab, λ(X : C),
            @SetoidType.Sym (F X) (a X) (b X) (ab X))

    definition LimMap.onElEl {C : CatType} {F G : C⟶SetoidCat}
            : (F ⟹ G) → LimSet F → LimSet G :=
        λ (nat : F ⟹ G), λ(a : LimType F), Setoid.MkLim
            /- atOb -/ ( λ(X : C), (nat /$$ X) $ (a X))
            /- atHom -/ ( λ(X Y : C), λ(m : X ⇒C⇒ Y),
                    ((nat /$$ Y) $/ (a m)) ⊡(G Y)⊡ ((nat /$$/ m) /$ (a X)))

    definition LimMap.onElEqu {C : CatType} {F G : C⟶SetoidCat}
            : ∀(nat : F ⟹ G), ∀{a b : LimSet F}, (a ≡(LimSet F)≡ b) →
                ((LimMap.onElEl nat a) ≡(LimSet G)≡ (LimMap.onElEl nat b)) :=
        λ (nat : F ⟹ G), λ (a b : LimSet F), λ (eq : a ≡(LimSet F)≡ b),
            λ (X : C), (nat /$$ X) $/ (eq X)

    definition LimMap.onEquEl {C : CatType} {F G : C⟶SetoidCat}
            : ∀{nat nat' : F ⟹ G}, ∀(eq : nat ≡(F ⟹ G)≡ nat'), ∀(a : LimSet F),
                ((LimMap.onElEl nat a) ≡(LimSet G)≡ (LimMap.onElEl nat' a)) :=
        λ (nat nat' : F ⟹ G), λ (eq : nat ≡(F ⟹ G)≡ nat'), λ (a : LimSet F),
            λ (X : C), (eq X) /$ (a X)

    definition LimMap {C : CatType} {F G : C⟶SetoidCat}
        : (F ⟹ G) ⥤ (LimSet F ⥤ LimSet G) :=
        Setoid.MkHom2 (F ⟹ G) (LimSet F) (LimSet G)
            LimMap.onElEl (@LimMap.onElEqu C F G) (@LimMap.onEquEl C F G)

    definition LimOnId {C : CatType}
        : Functor.OnIdProp (C⟶SetoidCat) SetoidCat (@LimSet C) (@LimMap C) :=
        λ(F : C⟶SetoidCat), λ(lim : LimSet F), λ(X : C),
            @SetoidType.Refl (F X) (lim X)

    definition LimOnMul {C : CatType}
        : Functor.OnMulProp (C⟶SetoidCat) SetoidCat (@LimSet C) (@LimMap C)
    := sorry

end Setoid

-- limit in SetoidCat
definition Setoid.Lim (C : CatType)
    : (C⟶SetoidCat)⟶SetoidCat :=
    Functor.MkOb
        (@Setoid.LimSet C)
        (@Setoid.LimMap C)
        (@Setoid.LimOnId C)
        (@Setoid.LimOnMul C)
