/- BigSigma.lean -/

import Setoid
import Cat
import Functor
import Over
import DepSet

namespace EXE

record BigSigmaType {Base : SetoidType} (P : DepSetoidCat Base) : Type :=
    (base : Base)
    (fiber : [P $$ base] )

definition BigSigma.Equ {Base : SetoidType} (P : DepSetoidCat Base)
        : EquType (BigSigmaType P) :=
    λ (a b : BigSigmaType P),
    (∃ eqbase : BigSigmaType.base a ≡Base≡ BigSigmaType.base b,
    (((P $$/ eqbase) $ (BigSigmaType.fiber a)) ≡(P $$ (BigSigmaType.base b))≡ (BigSigmaType.fiber b)))

definition BigSigma.Equ.base {Base : SetoidType} {P : DepSetoidCat Base}
    {a b : BigSigmaType P} (eq : BigSigma.Equ P a b)
        : BigSigmaType.base a ≡Base≡ BigSigmaType.base b :=
    exists.elim eq (λ eqbase eqfiber, eqbase)

definition BigSigma.Equ.fiber {Base : SetoidType} {P : DepSetoidCat Base}
    {a b : BigSigmaType P} (eq : BigSigma.Equ P a b)
        : (((P $$/ (BigSigma.Equ.base eq)) $ (BigSigmaType.fiber a)) ≡(P $$ (BigSigmaType.base b))≡ (BigSigmaType.fiber b)) :=
    exists.elim eq (λ eqbase eqfiber, eqfiber)

definition BigSigma.Refl {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.ReflProp (BigSigma.Equ P) :=
    λ (s0 : BigSigmaType P),
    exists.intro
        (@SetoidType.Refl Base (BigSigmaType.base s0))
        ((FunctorType.onId P) /$ (BigSigmaType.fiber s0))

definition BigSigma.Trans {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.TransProp (BigSigma.Equ P) :=
    λ (s1 s2 s3 : BigSigmaType P),
    λ (eq12 : BigSigma.Equ P s1 s2), λ (eq23 : BigSigma.Equ P s2 s3),
    exists.intro
        (@SetoidType.Trans Base
            (BigSigmaType.base s1)
            (BigSigmaType.base s2)
            (BigSigmaType.base s3)
            (BigSigma.Equ.base eq12)
            (BigSigma.Equ.base eq23))
        (@SetoidType.Trans3 (P $$ (BigSigmaType.base s3))
            ((P $$/ (@SetoidType.Trans Base
                        (BigSigmaType.base s1)
                        (BigSigmaType.base s2)
                        (BigSigmaType.base s3)
                        (BigSigma.Equ.base eq12)
                        (BigSigma.Equ.base eq23))) $
                (BigSigmaType.fiber s1))
            ((P $$/ (BigSigma.Equ.base eq23)) $
                ((P $$/ (BigSigma.Equ.base eq12)) $
                    (BigSigmaType.fiber s1)))
            ((P $$/ (BigSigma.Equ.base eq23)) $
                (BigSigmaType.fiber s2))
            (BigSigmaType.fiber s3)
            ((FunctorType.onMul P (BigSigma.Equ.base eq23) (BigSigma.Equ.base eq12)) /$
                (BigSigmaType.fiber s1))
            ((P $$/ (BigSigma.Equ.base eq23)) $/
                (BigSigma.Equ.fiber eq12))
            (BigSigma.Equ.fiber eq23))

definition BigSigma.Sym {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.SymProp (BigSigma.Equ P) :=
    λ (s1 s2 : BigSigmaType P),
    λ (eq12 : BigSigma.Equ P s1 s2),
    exists.intro
        (SetoidType.Sym Base (BigSigma.Equ.base eq12))
        (SetoidType.Sym
            (P $$ (BigSigmaType.base s1))
            (DepAdj P
                (BigSigma.Equ.base eq12)
                (SetoidType.Sym Base (BigSigma.Equ.base eq12))
                (BigSigmaType.fiber s1)
                (BigSigmaType.fiber s2)
                (BigSigma.Equ.fiber eq12)))

definition BigSigmaSet {Base : SetoidType} (P : DepSetoidCat Base)
    : SetoidType :=
    Setoid.MkOb
    /- El-/ (BigSigmaType P)
    /- Equ-/ (BigSigma.Equ P)
    /- Refl-/ (@BigSigma.Refl Base P)
    /- Trans -/ (@BigSigma.Trans Base P)
    /- Sym -/ (@BigSigma.Sym Base P)

definition BigSigmaFirst {Base : SetoidType} (P : DepSetoidCat Base)
        : BigSigmaSet P ⥤ Base :=
    Setoid.MkHom
        (BigSigmaType.base)
        (@BigSigma.Equ.base Base P)

definition BigSigmaOver (Base : SetoidType)
        : DepSetoidCat Base → OverSetoidCat Base :=
    λ P, OverType.mk
    /- Dom -/ (BigSigmaSet P)
    /- Hom -/ (BigSigmaFirst P)

definition BigSigmaFunctor (Base : SetoidType)
        : DepSetoidCat Base ⟶ OverSetoidCat Base :=
    Functor.MkOb
    /- onOb -/ ( λ(X : DepSetoidCat Base), BigSigmaOver Base X)
    /- onHom -/ ( λ(X Y : DepSetoidCat Base), sorry)
    /- onId -/ ( λ(X : DepSetoidCat Base), sorry)
    /- onMul -/ ( λ(X Y Z : DepSetoidCat Base), λ(g : Y ⇒_⇒ Z), λ(f : X ⇒_⇒ Y), sorry)

end EXE
