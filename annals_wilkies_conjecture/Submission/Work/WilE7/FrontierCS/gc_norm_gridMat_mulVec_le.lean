import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs

namespace Work.WilE7.FrontierCS

/-- Each entry of a `0/1` grid matrix has absolute value at most `1`. -/
lemma abs_gridMat_apply_le_one {d j : ℕ} (b : Fin d → Fin j → Bool) (k : Fin d) (c : Fin j) :
    |(gridMat b) k c| ≤ 1 := by
  simp only [gridMat, Matrix.of_apply]
  split <;> norm_num

lemma gc_norm_gridMat_mulVec_le {d j : ℕ} (b : Fin d → Fin j → Bool) (e : Fin j → ℝ) :
    ‖(Work.WilE7.FrontierCS.gridMat b).mulVec e‖ ≤ (j : ℝ) * ‖e‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [Matrix.mulVec_apply, Real.norm_eq_abs]
  calc |(fun j => (gridMat b) k j) ⬝ᵥ e|
      = |∑ c : Fin j, (gridMat b) k c * e c| := rfl
    _ ≤ ∑ c : Fin j, |(gridMat b) k c * e c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : Fin j, |(gridMat b) k c| * |e c| := by simp [abs_mul]
    _ ≤ ∑ _c : Fin j, ‖e‖ := by
        apply Finset.sum_le_sum
        intro c _
        have hec : |e c| ≤ ‖e‖ := by
          have h := norm_le_pi_norm e c
          rwa [Real.norm_eq_abs] at h
        calc |(gridMat b) k c| * |e c| ≤ 1 * |e c| :=
              mul_le_mul_of_nonneg_right (abs_gridMat_apply_le_one b k c) (abs_nonneg _)
          _ = |e c| := by ring
          _ ≤ ‖e‖ := hec
    _ = (j : ℝ) * ‖e‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.WilE7.FrontierCS
