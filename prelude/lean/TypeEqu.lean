/- TypeEqu -/

import Setoid

universe variable u

definition TypeEqu (T1 T2 : Type.{u+1}) : Type.{u} := 
    (∀ (P : Π (t1 t2 : Type.{u+1}), Type.{u}), 
        ∀ (refl : ∀ (t : Type.{u+1}), P t t), 
        -- the following is redundant:
        ∀ (trans : ∀ (t1 t2 t3 : Type.{u+1}), P t1 t2 → P t2 t3 → P t1 t3), 
        ∀ (sym : ∀ (t1 t2 : Type.{u+1}), P t1 t2 → P t2 t1), 
     P T1 T2)

definition TypesSetoid : Setoid := Setoid_Ob.mk
  (Type.{u+1})
  (TypeEqu.{u})
  (λ T, λ P refl trans sym, refl T)
  (λ T1 T2 T3, λ e12 e23, λ P refl trans sym, trans T1 T2 T3 (e12 P refl trans sym) (e23 P refl trans sym))
  (λ T1 T2, λ e12, λ P refl trans sym, sym T1 T2 (e12 P refl trans sym))

set_option pp.universes true
check TypeEqu

/-
Что мне надо проверить - что при использовании в индукции "сетоида типов" нам (1) достаточно транзитивности (=умножения), и нет необходимости во всех этих "ассоциативностях ассоциативности". Но пока это не факт, они могут где-то неожиданно вылезти. Иначе надо либо (2) добавлять аксиому К (единственности равенства на типах), либо (3) давать инф-группоиды в качестве кодировки универсумов (т.е. лезть в НоТТ), либо (4) как Альтенкирк моделировать универсум пользовательским индуктивно-индуктивным типом.
либо вообще (5) описывать инициальную категорию, в которой существуют все индуктивные типы (которая тоже будет кодироваться пределом, но таки гораздо сложнее)
-/