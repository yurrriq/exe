import Setoid
import Cat
import Functor
import Over
import DepSet

namespace EXE

record SigmaType {Base : SetoidType} (P : DepSetoidCat Base) : Type :=
    (base : Base)
    (fiber : [P $$ base] )

definition Sigma.Equ {Base : SetoidType} (P : DepSetoidCat Base)
        : EquType (SigmaType P) :=
    λ (a b : SigmaType P),
    (∃ eqbase : (SigmaType.base a ≡Base≡ SigmaType.base b),
    (((P $$/ eqbase) $ (SigmaType.fiber a)) ≡(P $$ (SigmaType.base b))≡ (SigmaType.fiber b)))

definition Sigma.Refl {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.ReflType (Sigma.Equ P) :=
    λ (a : SigmaType P),
    exists.intro (@SetoidType.Refl Base (SigmaType.base a))
        sorry

definition SigmaSet {Base : SetoidType} (P : DepSetoidCat Base)
    : SetoidType :=
    Setoid.MkOb
    /- El-/ (SigmaType P)
    /- Equ-/ (Sigma.Equ P)
    /- Refl-/ (sorry)
    /- Trans -/ (sorry)
    /- Sym -/ (sorry)

definition SigmaFirst {Base : SetoidType} (P : DepSetoidCat Base)
        : SigmaSet P ⥤ Base :=
    Setoid.MkHom
        (SigmaType.base)
        (λ a b, λ (eq : Sigma.Equ P a b),
            exists.elim eq (
                λ (eqbase : (SigmaType.base a ≡Base≡ SigmaType.base b)),
                λ (eqfiber : (((P $$/ eqbase) $ (SigmaType.fiber a)) ≡(P $$ (SigmaType.base b))≡ (SigmaType.fiber b))),
                eqbase ))

definition SigmaOver (Base : SetoidType)
        : DepSetoidCat Base → OverSetoidCat Base :=
    λ P, OverType.mk
    /- Dom -/ (SigmaSet P)
    /- Hom -/ (SigmaFirst P)

definition SigmaFunctor (Base : SetoidType)
        : DepSetoidCat Base ⟶ OverSetoidCat Base :=
    Functor.MkOb
    /- onOb -/ ( λ(X : DepSetoidCat Base), SigmaOver Base X)
    /- onHom -/ ( λ(X Y : DepSetoidCat Base), sorry)
    /- onId -/ ( λ(X : DepSetoidCat Base), sorry)
    /- onMul -/ ( λ(X Y Z : DepSetoidCat Base), λ(g : Y ⇒_⇒ Z), λ(f : X ⇒_⇒ Y), sorry)

end EXE
