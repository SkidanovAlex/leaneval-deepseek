import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.volume_rNorm_ball

/-!
# The `rNorm`-ball `{x | rNorm x ≤ R}` has finite Lebesgue measure

For `ι = Fin (n+1)` the set `{x : ι → ℝ | Work.HP.rNorm x ≤ R}` is either empty
(when `R < 0`) or the closed `L²`-ball of radius `R`, whose volume is computed by
`MeasureTheory.volume_sum_rpow_le`.  In both cases the measure is not `⊤`.
-/

namespace Work.HP.HP2

theorem volume_rNorm_le_ne_top (n : ℕ) (R : ℝ) :
    MeasureTheory.volume {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ R} ≠ ⊤ := by
  -- `rNorm` is the `L²` expression appearing in `volume_sum_rpow_le` with `p = 2`.
  have hrw : ∀ w : Fin (n + 1) → ℝ,
      Work.HP.rNorm w = (∑ i, |w i| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    intro w
    rw [Work.HP.rNorm, Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_two, sq_abs]
  by_cases hR : 0 ≤ R
  · -- rewrite the set as the closed `L²`-ball and apply the explicit volume formula
    rw [show {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ R}
        = {x : Fin (n + 1) → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ R} from by
      ext w
      simp only [Set.mem_ofPred_eq]
      rw [hrw w],
      MeasureTheory.volume_sum_rpow_le (ι := Fin (n + 1)) (p := 2) (by norm_num) R,
      (ENNReal.ofReal_pow hR (Fintype.card (Fin (n + 1)))).symm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · -- for `R < 0` the set is empty
    have hempty : {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ R} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hnn : (0 : ℝ) ≤ Work.HP.rNorm w := by
        rw [Work.HP.rNorm]; exact Real.sqrt_nonneg _
      exact not_le.mpr (lt_of_lt_of_le (not_le.mp hR) hnn)
    rw [hempty, MeasureTheory.measure_empty]
    exact ENNReal.zero_ne_top

end Work.HP.HP2
