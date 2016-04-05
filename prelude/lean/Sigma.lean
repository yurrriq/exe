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
    (∃ eqbase : SigmaType.base a ≡Base≡ SigmaType.base b,
    (((P $$/ eqbase) $ (SigmaType.fiber a)) ≡(P $$ (SigmaType.base b))≡ (SigmaType.fiber b)))

definition Sigma.Equ.base {Base : SetoidType} {P : DepSetoidCat Base}
    {a b : SigmaType P} (eq : Sigma.Equ P a b)
        : SigmaType.base a ≡Base≡ SigmaType.base b :=
    exists.elim eq (λ eqbase eqfiber, eqbase)

definition Sigma.Equ.fiber {Base : SetoidType} {P : DepSetoidCat Base}
    {a b : SigmaType P} (eq : Sigma.Equ P a b)
        : (((P $$/ (Sigma.Equ.base eq)) $ (SigmaType.fiber a)) ≡(P $$ (SigmaType.base b))≡ (SigmaType.fiber b)) :=
    exists.elim eq (λ eqbase eqfiber, eqfiber)

definition Sigma.Refl {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.ReflProp (Sigma.Equ P) :=
    λ (s0 : SigmaType P),
    exists.intro
        (@SetoidType.Refl Base (SigmaType.base s0))
        ((FunctorType.onId P) /$ (SigmaType.fiber s0))

definition Sigma.Trans {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.TransProp (Sigma.Equ P) :=
    λ (s1 s2 s3 : SigmaType P),
    λ (eq12 : Sigma.Equ P s1 s2), λ (eq23 : Sigma.Equ P s2 s3),
    exists.intro
        (@SetoidType.Trans Base
            (SigmaType.base s1)
            (SigmaType.base s2)
            (SigmaType.base s3)
            (Sigma.Equ.base eq12)
            (Sigma.Equ.base eq23))
        (@SetoidType.Trans3 (P $$ (SigmaType.base s3))
            ((P $$/ (@SetoidType.Trans Base
                        (SigmaType.base s1)
                        (SigmaType.base s2)
                        (SigmaType.base s3)
                        (Sigma.Equ.base eq12)
                        (Sigma.Equ.base eq23))) $
                (SigmaType.fiber s1))
            ((P $$/ (Sigma.Equ.base eq23)) $
                ((P $$/ (Sigma.Equ.base eq12)) $
                    (SigmaType.fiber s1)))
            ((P $$/ (Sigma.Equ.base eq23)) $
                (SigmaType.fiber s2))
            (SigmaType.fiber s3)
            ((FunctorType.onMul P (Sigma.Equ.base eq23) (Sigma.Equ.base eq12)) /$
                (SigmaType.fiber s1))
            ((P $$/ (Sigma.Equ.base eq23)) $/
                (Sigma.Equ.fiber eq12))
            (Sigma.Equ.fiber eq23))

definition Sigma.Sym {Base : SetoidType} (P : DepSetoidCat Base)
        : Equ.SymProp (Sigma.Equ P) :=
    λ (s1 s2 : SigmaType P),
    λ (eq12 : Sigma.Equ P s1 s2),
    exists.intro
        (@SetoidType.Sym Base
            (SigmaType.base s1)
            (SigmaType.base s2)
            (Sigma.Equ.base eq12))
        (@SetoidType.Trans (P $$ (SigmaType.base s1))
            ((P $$/ (@SetoidType.Sym Base
                        (SigmaType.base s1)
                        (SigmaType.base s2)
                        (Sigma.Equ.base eq12))) $
                (SigmaType.fiber s2))
            ((P $$/ (@SetoidType.Sym Base
                        (SigmaType.base s1)
                        (SigmaType.base s2)
                        (Sigma.Equ.base eq12))) $
                ((P $$/ (Sigma.Equ.base eq12)) $
                    (SigmaType.fiber s1)))
            (SigmaType.fiber s1)
            (@SetoidType.Sym (P $$ (SigmaType.base s1))
                ((P $$/ (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))) $
                    ((P $$/ (Sigma.Equ.base eq12)) $
                        (SigmaType.fiber s1)))
                ((P $$/ (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))) $
                    (SigmaType.fiber s2))
                ((P $$/ (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))) $/
                    (Sigma.Equ.fiber eq12)))
            ((@SetoidType.Trans3 (P $$ (SigmaType.base s1))
                ((P $$/ (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))) $
                    ((P $$/ (Sigma.Equ.base eq12)) $
                        (SigmaType.fiber s1)))
                ((P $$/ (@SetoidType.Trans Base
                    (SigmaType.base s1)
                    (SigmaType.base s2)
                    (SigmaType.base s1)
                    (Sigma.Equ.base eq12)
                    (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))))
                    $ (SigmaType.fiber s1))
                ((P $$/ (@SetoidType.Refl Base (SigmaType.base s1)))
                    $  (SigmaType.fiber s1))
                (SigmaType.fiber s1)
                ((FunctorType.onMulInv P
                    (@SetoidType.Sym Base
                            (SigmaType.base s1)
                            (SigmaType.base s2)
                            (Sigma.Equ.base eq12))
                    (Sigma.Equ.base eq12)) /$ (SigmaType.fiber s1))
                ((P $$// (true.intro)) /$ (SigmaType.fiber s1))
                ((FunctorType.onId P))) /$ (SigmaType.fiber s1)))

definition SigmaSet {Base : SetoidType} (P : DepSetoidCat Base)
    : SetoidType :=
    Setoid.MkOb
    /- El-/ (SigmaType P)
    /- Equ-/ (Sigma.Equ P)
    /- Refl-/ (@Sigma.Refl Base P)
    /- Trans -/ (@Sigma.Trans Base P)
    /- Sym -/ (@Sigma.Sym Base P)

definition SigmaFirst {Base : SetoidType} (P : DepSetoidCat Base)
        : SigmaSet P ⥤ Base :=
    Setoid.MkHom
        (SigmaType.base)
        (@Sigma.Equ.base Base P)

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
