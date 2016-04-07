/- Pi.lean -/

namespace EXE

universe variable a
universe variable b
constant ImperdicativePi : Π {A : Type.{a}}, (A → Type.{b}) → Type.{b}

abbreviation ℿ {A : Type.{a}} := @ImperdicativePi A

end EXE
