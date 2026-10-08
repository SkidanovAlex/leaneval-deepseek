import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

theorem ncard_of_insert_range_card {Ω ι : Type*} [Finite Ω] {V : Set Ω} {a : Ω} {f : ι → Ω}
    (hV : V = insert a (Set.range f)) (ha : a ∉ Set.range f) (hf : Function.Injective f) :
    V.ncard = Nat.card ι + 1 := by
  rw [hV, Set.ncard_insert_of_notMem ha, Set.ncard_range_of_injective hf]

end Work.AppXIShadow
