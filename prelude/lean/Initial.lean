/- Initial -/

import Setoid
import Cat
import Mor
import Functor
import Adjunction

set_option pp.universes true
set_option pp.metavar_args false
universe variable o1
universe variable h1
universe variable o2
universe variable h2
universe variable o3
universe variable h3

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

definition Initial.FromLim {C : CatType.{o1 h1}} (lim : HaveAllLim.{o1 h1 o1 h1} C) : C
    := RightAdj.Right (lim C) 𝟙

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

definition Terminal.FromColim {C : CatType.{o1 h1}} (colim : HaveAllColim.{o1 h1 o1 h1} C) : C
    := LeftAdj.Left (colim C) 𝟙
