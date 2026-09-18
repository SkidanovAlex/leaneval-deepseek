import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_volume_of_le

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Commons.NumberTheory.DuffinSchaeffer

theorem approxAddOrderOf_volume_eq_two_mul_Icc (X Y : ℕ) (hX : X ≠ 0) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n) (hsmall : ∀ n : ℕ, (n : ℝ) * δ n ≤ 1 / 2) :
    (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (δ q))) =
      ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * δ q) := by
  classical
  have hX1 : 1 ≤ X := by omega
  have hnonneg : ∀ q ∈ Finset.Icc X Y, 0 ≤ 2 * (q.totient : ℝ) * δ q := by
    intro q hq
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg q.totient)) (hδ q)
  calc
    (∑ q ∈ Finset.Icc X Y, MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (δ q)))
        = ∑ q ∈ Finset.Icc X Y, ENNReal.ofReal (2 * (q.totient : ℝ) * δ q) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hqX : X ≤ q := (Finset.mem_Icc.mp hq).1
            have hqpos : 0 < q := by omega
            have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
            have hsmall2 : 2 * δ q ≤ 1 / (q : ℝ) := by
              rw [le_div_iff₀ hqR]
              nlinarith [hsmall q]
            calc
              MeasureTheory.volume (approxAddOrderOf UnitAddCircle q (δ q))
                  = (q.totient : ENNReal) * ENNReal.ofReal (2 * δ q) :=
                      approxAddOrderOf_volume_of_le q hqpos (δ q) (hδ q) hsmall2
              _ = ENNReal.ofReal ((q.totient : ℝ) * (2 * δ q)) := by
                  rw [← ENNReal.ofReal_natCast (q.totient)]
                  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (q.totient : ℝ))]
              _ = ENNReal.ofReal (2 * (q.totient : ℝ) * δ q) := by
                  congr 1
                  ring
    _ = ENNReal.ofReal (∑ q ∈ Finset.Icc X Y, 2 * (q.totient : ℝ) * δ q) := by
        rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
    _ = ENNReal.ofReal (2 * ∑ q ∈ Finset.Icc X Y, (q.totient : ℝ) * δ q) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro q hq
        ring

end Commons.NumberTheory.DuffinSchaeffer
