
import Setoid
import Cat
import Functor

set_option pp.universes true
set_option pp.metavar_args false
universe variable u

definition DepSetoidType (Base : SetoidType) : Type :=
    (Cat.FromSet Base) ⟶ SetoidCat
definition DepSetoid.HomSet {Base : SetoidType} : Cat.HomType (DepSetoidType Base) :=
    @Functor.HomSet (Cat.FromSet Base) SetoidCat
definition DepSetoid.Id {Base : SetoidType} : Cat.IdType (@DepSetoid.HomSet Base) :=
    @Functor.Id (Cat.FromSet Base) SetoidCat
definition DepSetoid.Mul {Base : SetoidType} : Cat.MulType (@DepSetoid.HomSet Base) :=
    @Functor.Mul (Cat.FromSet Base) SetoidCat
definition DepSetoid.UnitL {Base : SetoidType} : Cat.UnitLProp (@DepSetoid.Id Base) (@DepSetoid.Mul Base) :=
    @Functor.UnitL (Cat.FromSet Base) SetoidCat
definition DepSetoid.UnitR {Base : SetoidType} : Cat.UnitRProp (@DepSetoid.Id Base) (@DepSetoid.Mul Base) :=
    @Functor.UnitR (Cat.FromSet Base) SetoidCat
definition DepSetoid.Assoc {Base : SetoidType} : Cat.AssocProp (@DepSetoid.Mul Base) :=
    @Functor.Assoc (Cat.FromSet Base) SetoidCat

definition DepSetoidCat (Base : SetoidType) : CatType :=
    Cat.MkOb
        (DepSetoidType Base)
        (@DepSetoid.HomSet Base)
        (@DepSetoid.Id Base) (@DepSetoid.Mul Base)
        (@DepSetoid.UnitL Base) (@DepSetoid.UnitR Base) (@DepSetoid.Assoc Base)
