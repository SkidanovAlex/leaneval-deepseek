import Mathlib

namespace Work.OROneRel

theorem mk_flatten_prod {γ : Type*} (L : List (List (γ × Bool))) :
    FreeGroup.mk L.flatten = (L.map FreeGroup.mk).prod := by
  induction L with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons a l ih =>
      rw [List.flatten_cons, List.map_cons, List.prod_cons, ← FreeGroup.mul_mk, ih]

end Work.OROneRel
