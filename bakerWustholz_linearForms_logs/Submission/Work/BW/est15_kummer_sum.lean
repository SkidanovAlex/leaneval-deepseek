import Mathlib
import Submission.Work.BW.prod_formula_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- The Kummer (2-adic) term summed over the finite places: `∑ᶠ_v (-log |2|_v) = d·log 2` where `d = [K:ℚ]`. Indeed, the logarithmic product formula for `2 : K` gives `∑_{v infinite} mult v · log 2 + ∑ᶠ_{v finite} log |2|_v = 0` (using `InfinitePlace.map_natCast`), and `∑_{v infinite} mult v = d` (`NumberField.InfinitePlace.sum_mult_eq`). Follows from `Work.BW.prod_formula_log (x := (2 : K))`. -/
theorem est15_kummer_sum {K : Type*} [Field K] [NumberField K] :
    (∑ᶠ v : NumberField.FinitePlace K, - Real.log (v (2 : K)))
      = (Module.finrank ℚ K : ℝ) * Real.log 2 := by
  -- Logarithmic product formula for `2 : K`.
  have hpf := prod_formula_log (K := K) (x := (2 : K)) (by norm_num)
  -- `(2 : K)` is the image of the natural number `2`, so at every infinite place it has
  -- absolute value `2`.
  have h2c : (2 : K) = ((2 : ℕ) : K) := by norm_num
  have h : ∀ v : NumberField.InfinitePlace K, v (2 : K) = (2 : ℝ) := by
    intro v; rw [h2c, NumberField.InfinitePlace.map_natCast]; norm_num
  -- The archimedean part of the product formula is `[K : ℚ] · log 2`.
  have hsum : (∑ v : NumberField.InfinitePlace K, ((v.mult : ℕ) : ℝ) * Real.log (v (2 : K)))
      = (Module.finrank ℚ K : ℝ) * Real.log 2 := by
    simp only [h]
    rw [← Finset.sum_mul]
    congr 1
    have := NumberField.InfinitePlace.sum_mult_eq (K := K)
    rw [← this]
    push_cast
    rfl
  rw [hsum] at hpf
  rw [finsum_neg_distrib]
  linarith

end Work.BW
