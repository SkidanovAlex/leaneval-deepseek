import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- `rNorm` is the `L²` norm written with `rpow`, matching the expression
`(∑ i, |x i| ^ p) ^ (1/p)` used by Mathlib's `volume_sum_rpow_lt` / `volume_sum_rpow_le`. -/
lemma rNorm_eq_sum_rpow {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    rNorm w = (∑ i, |w i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [rNorm, Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_ofNat, sq_abs]

theorem volume_rNorm_ball_lt {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume {w : ι → ℝ | Work.HP.rNorm w < r}
      = ENNReal.ofReal (r ^ Fintype.card ι)
        * MeasureTheory.volume {w : ι → ℝ | Work.HP.rNorm w ≤ 1} := by
  have hlt : {w : ι → ℝ | rNorm w < r}
      = {x : ι → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) < r} := by
    ext w; simp only [Set.mem_ofPred_eq, rNorm_eq_sum_rpow]
  have hle : {w : ι → ℝ | rNorm w ≤ 1}
      = {x : ι → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ 1} := by
    ext w; simp only [Set.mem_ofPred_eq, rNorm_eq_sum_rpow]
  rw [hlt, hle, MeasureTheory.volume_sum_rpow_lt ι (p := 2) (by norm_num) r,
      MeasureTheory.volume_sum_rpow_le ι (p := 2) (by norm_num) 1]
  rw [ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_pow hr]

end Work.HP
