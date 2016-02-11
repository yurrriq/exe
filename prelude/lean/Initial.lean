/- Initial -/

import Setoid
import Cat
import Mor
import Functor
import Adjunction

record InitialType (C : CatType) (Obj : C) : Type :=
    (Cone : Functor.ConeType Obj 𝟙)
    (IsCone : Functor.IsConeProp Obj 𝟙 Cone)
    (Ok : Cone Obj ≡(Obj ⇒C⇒ Obj)≡ ①)

lemma Initial.UniqueHom.util {C : CatType} (A B : C) (initA : InitialType C A)
    (f : A ⇒C⇒ B) : (InitialType.Cone initA B) ≡(A ⇒C⇒ B)≡ f
:= (InitialType.IsCone initA f) ⊡_⊡
    (hom_and_eq C f (InitialType.Ok initA)) ⊡_⊡
    (CatType.UnitR C f)

lemma Initial.UniqueHom {C : CatType} {I : C} (init : InitialType C I)
    : ∀{X : C}, Setoid.SingletonProp (I ⇒C⇒ X)
:= λ(X : C), λ(f g : I ⇒C⇒ X),
        (SetoidType.Sym _ (Initial.UniqueHom.util I X init f)) ⊡_⊡
        (Initial.UniqueHom.util I X init g)

record TerminalType (C : CatType) (Obj : C) : Type :=
    (Cocone : Functor.CoconeType 𝟙 Obj)
    (IsCocone : Functor.IsCoconeProp 𝟙 Obj Cocone)
    (Ok : ① ≡(Obj ⇒C⇒ Obj)≡ Cocone Obj)

lemma Terminal.UniqueHom.util {C : CatType} (A B : C) (termB : TerminalType C B)
    (f : A ⇒C⇒ B) : f ≡(A ⇒C⇒ B)≡ (TerminalType.Cocone termB A)
:= (CatType.UnitLInv C f) ⊡_⊡
    (eq_and_hom C (TerminalType.Ok termB) f) ⊡_⊡
    (TerminalType.IsCocone termB f)

lemma Terminal.UniqueHom {C : CatType} {T : C} (term : TerminalType C T)
    : ∀{X : C}, Setoid.SingletonProp (X ⇒C⇒ T)
:= λ(X : C), λ(f g : X ⇒C⇒ T),
        (Terminal.UniqueHom.util X T term f) ⊡_⊡
        (SetoidType.Sym _ (Terminal.UniqueHom.util X T term g))
