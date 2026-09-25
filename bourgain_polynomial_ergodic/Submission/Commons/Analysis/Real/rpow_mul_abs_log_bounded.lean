import Mathlib
import Submission.Commons.Analysis.Laplace.halfplane_continuation

namespace Commons.Analysis.Real

/-- Uniform bound for `t ^ a * (-log t)` on `(0, 1]`: substituting `u = -log t` this is the
elementary estimate `u * exp (-a * u) ≤ 1 / a` (a special case of
`Commons.Analysis.Laplace.abs_mul_exp_neg_le_inv`). -/
private lemma rpow_mul_neg_log_le {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t ^ a * (-Real.log t) ≤ 1 / a := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hu : 0 ≤ -Real.log t := neg_nonneg.mpr hlog
  have h := Commons.Analysis.Laplace.abs_mul_exp_neg_le_inv ha hu
  rw [abs_of_nonneg hu] at h
  have hrew : t ^ a = Real.exp (-a * (-Real.log t)) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  rw [hrew, mul_comm]
  exact h

theorem rpow_mul_abs_log_bounded {a M : ℝ} (ha : 0 < a) (hM : 0 < M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ M → t ^ a * |Real.log t| ≤ K := by
  refine ⟨1 / a + M ^ a * |Real.log M|, ?_, ?_⟩
  · have h1 : 0 ≤ 1 / a := div_nonneg zero_le_one ha.le
    have h2 : 0 ≤ M ^ a * |Real.log M| :=
      mul_nonneg (Real.rpow_nonneg hM.le a) (abs_nonneg _)
    linarith
  · intro t ht htM
    have hD : 0 ≤ M ^ a * |Real.log M| :=
      mul_nonneg (Real.rpow_nonneg hM.le a) (abs_nonneg _)
    by_cases h1 : t ≤ 1
    · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le h1
      have habs : |Real.log t| = -Real.log t := abs_of_nonpos hlog
      rw [habs]
      have hb := rpow_mul_neg_log_le ha ht h1
      linarith
    · have h1' : 1 < t := not_le.mp h1
      have hMt : 1 ≤ M := le_trans h1'.le htM
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg h1'.le
      have hlogM : 0 ≤ Real.log M := Real.log_nonneg hMt
      have habs : |Real.log t| = Real.log t := abs_of_nonneg hlogt
      have habsM : |Real.log M| = Real.log M := abs_of_nonneg hlogM
      rw [habs]
      have hrpow : t ^ a ≤ M ^ a := Real.rpow_le_rpow ht.le htM ha.le
      have hlogle : Real.log t ≤ Real.log M := Real.log_le_log ht htM
      have hprod : t ^ a * Real.log t ≤ M ^ a * Real.log M :=
        mul_le_mul hrpow hlogle hlogt (Real.rpow_nonneg hM.le a)
      have hgoal : M ^ a * Real.log M ≤ 1 / a + M ^ a * |Real.log M| := by
        rw [habsM]
        exact le_add_of_nonneg_left (div_nonneg zero_le_one ha.le)
      linarith

end Commons.Analysis.Real
