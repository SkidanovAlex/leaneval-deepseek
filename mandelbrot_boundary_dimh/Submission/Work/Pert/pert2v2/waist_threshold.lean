import Mathlib
import Submission.Work.Pert.Ksub2.exists_log_le_half

namespace Work.Pert.pert2v2

theorem waist_threshold {Ξ A C R₂ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hR₂ : 0 < R₂) :
    ∃ H : ℝ, 0 < H ∧ ∀ t : ℝ, H ≤ t →
      1 + Ξ ≤ t / 2 ∧ R₂ ≤ t / 8 ∧ A * Real.log (t + 3) + C + (t + 1) / 64 < t / 32 := by
  -- The logarithm is dominated by the linear term; `exists_log_le_half` supplies the
  -- threshold `R'` for `512 A (1 + log · ) ≤ · / 2`.
  obtain ⟨R', hR'⟩ := Work.Pert.Ksub2.exists_log_le_half (512 * A)
  refine ⟨max 3 (max (2 * (1 + Ξ)) (max (8 * R₂) (max R' (512 * (C + 1) / 7 + 1)))), ?_, ?_⟩
  · -- positivity of the threshold, from `8 R₂ > 0`
    have h : 8 * R₂ ≤
        max 3 (max (2 * (1 + Ξ)) (max (8 * R₂) (max R' (512 * (C + 1) / 7 + 1)))) :=
      le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith
  · intro t ht
    have h3 : (3:ℝ) ≤ t := le_trans (le_max_left _ _) ht
    have hΞ : 2 * (1 + Ξ) ≤ t :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hR2 : 8 * R₂ ≤ t :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) ht
    have hR't : R' ≤ t + 3 := by
      have : R' ≤ max 3 (max (2 * (1 + Ξ)) (max (8 * R₂) (max R' (512 * (C + 1) / 7 + 1)))) :=
        le_trans (le_max_left _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      linarith
    have hd : 512 * (C + 1) / 7 + 1 ≤ t :=
      le_trans (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) ht
    refine ⟨by linarith, by linarith, ?_⟩
    have hlog : 512 * A * (1 + Real.log (t + 3)) ≤ (t + 3) / 2 := hR' (t + 3) hR't
    have hlog2 : 512 * A * (1 + Real.log (t + 3)) ≤ t := by linarith
    have hAlog : A * Real.log (t + 3) ≤ t / 512 := by
      have h2 : A * (1 + Real.log (t + 3)) ≤ t / 512 := by linarith
      have hl : Real.log (t + 3) ≤ 1 + Real.log (t + 3) := by linarith
      calc A * Real.log (t + 3) ≤ A * (1 + Real.log (t + 3)) := mul_le_mul_of_nonneg_left hl hA
        _ ≤ t / 512 := h2
    have hCt : C < t / 64 - t / 512 - 1 / 64 := by linarith
    linarith

end Work.Pert.pert2v2
