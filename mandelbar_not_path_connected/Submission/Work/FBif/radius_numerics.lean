import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- Elementary bound on the escape-radius radical: for `s ≥ 0`, `√(1 + 4s) ≤ 8s + 5`. -/
theorem radius_numerics_sqrt_bound (s : ℝ) (hs : 0 ≤ s) :
    Real.sqrt (1 + 4 * s) ≤ 8 * s + 5 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (8 * s + 5), sq_nonneg s, hs]

/-- `√(1 + 4‖c‖) ≤ farRad c - 3`: the escape radical stays below the far radius. -/
theorem radius_numerics_sqrt_farRad (c : ℂ) :
    Real.sqrt (1 + 4 * ‖c‖) ≤ farRad c - 3 := by
  have h1 : Real.sqrt (1 + 4 * ‖c‖) ≤ 8 * ‖c‖ + 5 :=
    radius_numerics_sqrt_bound ‖c‖ (norm_nonneg c)
  have h2 : 8 * (‖c‖ + 1) ≤ farRad c := le_max_right _ _
  linarith

theorem radius_numerics (c : ℂ) :
    0 < Work.FBif.farRad c ∧ 0 < Work.FBif.innerRad c ∧ 0 < Work.FBif.cutRad c ∧
      Work.FBif.innerRad c < Work.FBif.cutRad c ∧
      Work.FBif.cutRad c < Work.FBif.farRad c ∧ Work.FBif.escR c + 1 ≤ Work.FBif.innerRad c ∧
      Work.FBif.farRad c + ‖c‖ + 1 ≤ (Work.FBif.innerRad c) ^ 2 ∧
      Work.FBif.farRad c + ‖c‖ ≤ (Work.FBif.cutRad c) ^ 2 := by
  have hc0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hf16 : 16 ≤ farRad c := le_max_left _ _
  have hf8 : 8 * (‖c‖ + 1) ≤ farRad c := le_max_right _ _
  have hfpos : 0 < farRad c := by linarith
  have hsqrt := radius_numerics_sqrt_farRad c
  refine ⟨hfpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [innerRad]; linarith
  · simp only [cutRad]; linarith
  · simp only [innerRad, cutRad]; linarith
  · simp only [cutRad]; linarith
  · simp only [escR, innerRad]; linarith
  · simp only [innerRad]; nlinarith [sq_nonneg (farRad c)]
  · simp only [cutRad]; nlinarith [sq_nonneg (farRad c)]

end Work.FBif
