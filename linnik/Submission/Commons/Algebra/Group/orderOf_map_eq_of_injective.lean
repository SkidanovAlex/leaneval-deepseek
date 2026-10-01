import Mathlib.GroupTheory.OrderOfElement

namespace Commons.Algebra.Group

theorem orderOf_map_eq_of_injective {G : Type*} {H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (hf : Function.Injective f) (a : G) :
    orderOf (f a) = orderOf a := by
  exact orderOf_injective f hf a

end Commons.Algebra.Group