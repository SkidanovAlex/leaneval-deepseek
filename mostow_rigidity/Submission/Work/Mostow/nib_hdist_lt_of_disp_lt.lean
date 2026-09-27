import Mathlib
import Submission.Work.Mostow.nearId_blk

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-!
# `nib_hdist_lt_of_disp_lt`: the forward direction of the two-scale criterion

This is the converse of `nib_disp_lt_of_hdist_lt` (proved in `nearId_blk`).  Both directions
rest on the exact identity `nib_cosh_hdist_blk`

  `cosh (hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W)) = 1 + ‖R W - W‖ ^ 2 / 2`,

together with `cosh η = 1 + 2 * sinh (η / 2) ^ 2` and the monotonicity/evenness identity
`Real.cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y|`.

Note that the hypothesis forces `η > 0`: `‖R W - W‖ ≥ 0` while `2 * sinh (η/2) > 0`.
-/

noncomputable section

theorem nib_hdist_lt_of_disp_lt (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) (η : ℝ)
    (h : ‖R W - W‖ < 2 * Real.sinh (η / 2)) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W) (Submission.Mostow.blk 1 m 1 R • Submission.Mostow.fermiW 1 m v W) < η := by
  have hDnn : 0 ≤ hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) :=
    nib_hdist_nonneg _ _
  -- the hypothesis forces `η > 0`
  have hs2pos : 0 < Real.sinh (η / 2) := by
    have := lt_of_le_of_lt (norm_nonneg (R W - W)) h
    linarith
  have hηpos : 0 < η := by
    have := Real.sinh_pos_iff.mp hs2pos
    linarith
  have hcoshη : Real.cosh η = 1 + 2 * Real.sinh (η / 2) ^ 2 := by
    have h2 := Real.cosh_two_mul (η / 2)
    rw [show (2 : ℝ) * (η / 2) = η by ring] at h2
    rw [h2, Real.cosh_sq]
    ring
  have hcosh : Real.cosh (hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W))
      < Real.cosh η := by
    rw [nib_cosh_hdist_blk m hA1 hI1 hA hI R v W, hcoshη]
    have hsq : ‖R W - W‖ ^ 2 < (2 * Real.sinh (η / 2)) ^ 2 := by
      have hsnn : 0 ≤ 2 * Real.sinh (η / 2) := by linarith [hs2pos]
      nlinarith [h, norm_nonneg (R W - W)]
    nlinarith [hsq]
  have habs := Real.cosh_lt_cosh.mp hcosh
  rwa [abs_of_nonneg hDnn, abs_of_pos hηpos] at habs

end

end Work.Mostow
