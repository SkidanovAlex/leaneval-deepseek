import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

/-- The sum of the multiplicities of the infinite places of a number field `K`, taken over all
places except a fixed place `v₀`, equals `[K : ℚ] - v₀.mult`. This is the "erase one place"
form of `NumberField.InfinitePlace.sum_mult_eq`. -/
theorem sum_mult_erase {K : Type*} [Field K] [NumberField K] [DecidableEq (NumberField.InfinitePlace K)]
    (v₀ : NumberField.InfinitePlace K) :
    (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ)) =
      (Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ) := by
  have hsum : (∑ x : NumberField.InfinitePlace K, (x.mult : ℝ)) = (Module.finrank ℚ K : ℝ) := by
    rw [← Nat.cast_sum, NumberField.InfinitePlace.sum_mult_eq]
  have h := Finset.add_sum_erase Finset.univ (fun v : NumberField.InfinitePlace K => (v.mult : ℝ))
    (Finset.mem_univ v₀)
  rw [hsum] at h
  linarith

end Work.BW.LiouvilleAux
