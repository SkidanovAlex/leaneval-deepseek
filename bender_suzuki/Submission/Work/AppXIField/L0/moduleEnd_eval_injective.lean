import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.L0

/-- For a simple module `V` over a ring `R`, evaluation at a nonzero vector is injective on the
endomorphism ring: if `k v = l v` with `v ≠ 0`, then `k = l`. Equivalently (Schur's lemma) every
nonzero endomorphism of a simple module is injective. -/
theorem moduleEnd_eval_injective {R V : Type} [Ring R] [AddCommGroup V] [Finite V] [Module R V]
    [IsSimpleModule R V] (v : V) (hv : v ≠ 0) :
    Function.Injective (fun k : Module.End R V => k v) := by
  intro k l hkl
  change k v = l v at hkl
  have hzero : (k - l) v = 0 := by rw [LinearMap.sub_apply, hkl, sub_self]
  rcases LinearMap.injective_or_eq_zero (k - l : Module.End R V) with hinj | h0
  · exact absurd (hinj (show (k - l) v = (k - l) 0 by rw [hzero, map_zero])) hv
  · exact sub_eq_zero.mp h0

end Work.AppXIField.L0
