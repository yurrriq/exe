/- Limit -/

import Setoid
import Mor
import Functor

/-
 - Definition of LIMIT
 -/

namespace Setoid
    record LimType {C : CatType} (F : C⟶SetoidCat) : Type :=
        (atOb : Π(X : C), [F X])
        (atHom : ∀{X Y : C}, ∀(m : X ⇒C⇒ Y), ((F m) $ (atOb X)) ≡(F Y)≡ (atOb Y))
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

    definition LimMap_onEl {C : CatType} {F G : C⟶SetoidCat}
            (nat : F ⟹ G) : (LimSet F ⥤ LimSet G) :=
        Setoid.MkHom
            /- onEl -/ ( λ(a : LimType F), Setoid.MkLim
                /- atOb -/ ( λ(X : C), (nat X) $ (a X))
                /- atHom -/ ( λ(X Y : C), λ(m : X ⇒C⇒ Y), sorry))
            /- onEqu -/ ( λ(a b : LimType F), λ (eq : ≡(LimType F)≡), sorry)

end Setoid

-- limit in SetoidCat
definition Setoid.Lim (C : CatType) : (C⟶SetoidCat)⟶SetoidCat :=
    Functor.MkOb
    (@Setoid.LimSet C) -- (onOb : (C⟶SetoidCat) → SetoidType)
    sorry -- (onHom : Π{F G : C⟶SetoidCat}, (F ⟹ G)⥤(onOb F ⥤ onOb G))
    sorry -- (onId : Functor.OnId C D onOb @onHom)
    sorry -- (onMul : Functor.OnMul C D onOb @onHom)
