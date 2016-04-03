/- DepSet.lean -/

import Setoid
import Cat
import Functor
import Over

set_option pp.universes true
set_option pp.metavar_args false

namespace EXE

definition DepSetoidCat (Base : SetoidType) : CatType := (Cat.FromSet Base) ⟶ SetoidCat

definition OverSetoidCat (Base : SetoidType) : CatType := OverCat SetoidCat Base

end EXE
