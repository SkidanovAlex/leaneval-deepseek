import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Decomposition of the logarithmic height of a nonzero tuple `x : ι → K` over a number field: the sum over the infinite places of `mult v · log (⨆ i, v (x i))`, plus the (finitely supported) sum over the finite places of `log (⨆ i, v (x i))`, equals `Height.logHeight x`. Immediate from `Height.logHeight_eq_log_mulHeight`, `NumberField.mulHeight_eq hx`, `Real.log_mul`, `Real.log_prod`, `Real.log_pow` and `Real.log_finprod`. -/
theorem est15_height_id {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (x : ι → K) (hx : x ≠ 0) :
    (∑ v : NumberField.InfinitePlace K, ((v.mult : ℕ) : ℝ) * Real.log (⨆ i, v (x i)))
      + (∑ᶠ v : NumberField.FinitePlace K, Real.log (⨆ i, v (x i)))
      = Height.logHeight x := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hpos_inf : ∀ v : NumberField.InfinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hi₀)
      (le_ciSup_of_le (f := fun i : ι => v (x i)) (Finite.bddAbove_range _) i₀ le_rfl)
  have hpos_fin : ∀ v : NumberField.FinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (NumberField.FinitePlace.pos_iff.mpr hi₀)
      (le_ciSup_of_le (f := fun i : ι => v (x i)) (Finite.bddAbove_range _) i₀ le_rfl)
  rw [Height.logHeight_eq_log_mulHeight, NumberField.mulHeight_eq hx]
  rw [Real.log_mul
      (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (ne_of_gt (hpos_inf v)))
      (finprod_ne_zero fun v => ne_of_gt (hpos_fin v))]
  congr 1
  · rw [Real.log_prod (s := Finset.univ)
        (f := fun v : NumberField.InfinitePlace K => (⨆ i, v (x i)) ^ v.mult)
        (fun v _ => pow_ne_zero _ (ne_of_gt (hpos_inf v)))]
    exact Finset.sum_congr rfl fun v _ => (Real.log_pow _ _).symm
  · rw [Real.log_finprod hpos_fin]

end Work.BW
