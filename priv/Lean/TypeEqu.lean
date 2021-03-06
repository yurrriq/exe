/- TypeEqu -/

import Setoid

set_option pp.universes true
set_option pp.metavar_args false
universe variable u
universe variable v

definition idd (A : Type.{u}) (a : A) : A := a

definition TypeEqu (T1 T2 : Type.{u}) : Type :=
    (Π (P : Π (t1 t2 : Type.{u}), Type.{v}),
        Π (refl : Π (t : Type.{u}), P t t),
        -- the following is redundant:
        Π (trans : Π (t1 t2 t3 : Type.{u}), P t1 t2 → P t2 t3 → P t1 t3),
        Π (sym : Π (t1 t2 : Type.{u}), P t1 t2 → P t2 t1),
     P T1 T2)
print TypeEqu

definition SetoidEqu (S1 S2 : Setoid) : Type := sorry



/-
Что мне надо проверить - что при использовании в индукции "сетоида типов" нам (1) достаточно транзитивности (=умножения), и нет необходимости во всех этих "ассоциативностях ассоциативности". Но пока это не факт, они могут где-то неожиданно вылезти. Иначе надо либо (2) добавлять аксиому К (единственности равенства на типах), либо (3) давать инф-группоиды в качестве кодировки универсумов (т.е. лезть в НоТТ), либо (4) как Альтенкирк моделировать универсум пользовательским индуктивно-индуктивным типом.
либо вообще (5) описывать инициальную категорию, в которой существуют все индуктивные типы (которая тоже будет кодироваться пределом, но таки гораздо сложнее)
-/
