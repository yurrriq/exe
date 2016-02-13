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

lemma Initial.Singleton {C : CatType} {I : C} (init : InitialType C I) (X : C)
    : Setoid.SingletonType (I ⇒C⇒ X)
:= Setoid.MkSingleton
        ( InitialType.Cone init X)
        ( λ(f : I ⇒C⇒ X),
            (InitialType.IsCone init f) ⊡_⊡
            (f ⊙C⊙/ (InitialType.Ok init)) ⊡_⊡
            (CatType.UnitR C f) )

record TerminalType (C : CatType) (Obj : C) : Type :=
    (Cocone : Functor.CoconeType 𝟙 Obj)
    (IsCocone : Functor.IsCoconeProp 𝟙 Obj Cocone)
    (Ok : Cocone Obj ≡(Obj ⇒C⇒ Obj)≡ ①)

lemma Terminal.Singleton {C : CatType} {T : C} (term : TerminalType C T) (X : C)
    : Setoid.SingletonType (X ⇒C⇒ T)
:= Setoid.MkSingleton
        ( TerminalType.Cocone term X)
        ( λ(g : X ⇒C⇒ T),
            (SetoidType.Sym _ (TerminalType.IsCocone term g)) ⊡_⊡
            ((TerminalType.Ok term) /⊙C⊙ g) ⊡_⊡
            (CatType.UnitL C g))
