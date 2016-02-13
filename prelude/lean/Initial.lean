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
print InitialType

namespace Initial

    abbreviation MkI {C : CatType} {Obj : C}
    := @InitialType.mk C Obj

    lemma Singleton {C : CatType} {I : C}
        (init : InitialType C I) (X : C)
        : Setoid.SingletonType (I ⇒C⇒ X)
    := Setoid.MkSingleton
            ( InitialType.Cone init X)
            ( λ(f : I ⇒C⇒ X),
                (InitialType.IsCone init f) ⊡_⊡
                (f ⊙C⊙/ (InitialType.Ok init)) ⊡_⊡
                (CatType.UnitR C f) )

    definition FromLim {C : CatType.{o1 h1}}
        (lim : HaveAllLim.{o1 h1 o1 h1} C)
        : C
    := Lim.Apply lim 𝟙
    print FromLim

    definition FromLim.Ok {C : CatType.{o1 h1}}
        (lim : HaveAllLim.{o1 h1 o1 h1} C)
        : InitialType C ((RightAdj.Right (lim C)) $$ 𝟙) -- (Lim.Apply lim 𝟙)
    :=
        proof
            MkI
                -- ( Functor.CoconeFromNat (Lim.Prj lim 𝟙) )
                ( λ X, ((AdjType.counit (RightAdj.adj (lim C))) /$$ 𝟙) /$$ X)
                -- ( Functor.IsCoconeFromNat (Lim.Prj lim 𝟙) )
                ( λ A B, λ(m : A ⇒C⇒ B),
                    proof
                        (CatType.UnitRInv C ((((AdjType.counit (RightAdj.adj (lim C))) /$$ 𝟙)) /$$ B))
                            ⊡(((RightAdj.Right (lim C)) $$ 𝟙) ⇒C⇒ B)⊡
                        (((AdjType.counit (RightAdj.adj (lim C))) /$$ 𝟙) /$$/ m)
                    qed )
                ( sorry )
        qed

end Initial

record TerminalType (C : CatType) (Obj : C) : Type :=
    (Cocone : Functor.CoconeType 𝟙 Obj)
    (IsCocone : Functor.IsCoconeProp 𝟙 Obj Cocone)
    (Ok : Cocone Obj ≡(Obj ⇒C⇒ Obj)≡ ①)

namespace Terminal

    abbreviation Mk {C : CatType} {Obj : C}
    := @TerminalType.mk C Obj

    lemma Singleton {C : CatType} {T : C} (term : TerminalType C T) (X : C)
        : Setoid.SingletonType (X ⇒C⇒ T)
    := Setoid.MkSingleton
            ( TerminalType.Cocone term X)
            ( λ(g : X ⇒C⇒ T),
                (SetoidType.Sym _ (TerminalType.IsCocone term g)) ⊡_⊡
                ((TerminalType.Ok term) /⊙C⊙ g) ⊡_⊡
                (CatType.UnitL C g))

    definition Terminal.FromColim {C : CatType.{o1 h1}} (colim : HaveAllColim.{o1 h1 o1 h1} C)
        : C
    := Colim.Apply colim 𝟙

end Terminal
