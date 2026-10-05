import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs

namespace Work.RPB.B5

/-- The affine middle branch has constant derivative `π²/32`, and the quadratic branch has
strictly positive derivative on `(-√2, ∞)`. -/
theorem deriv_rhoMid_rhoQuad (x : ℝ) (hx : -Real.sqrt 2 < x) :
    deriv rhoMid x = Real.pi ^ 2 / 32 ∧ 0 < deriv rhoQuad x := by
  constructor
  · -- `rhoMid` is affine: `rhoMid y = π²/32 · (1 + y + √2)`.
    unfold rhoMid
    simp
  · -- `rhoQuad y = π²/4 · (1 + y/√2)²`, whose derivative is
    -- `π²/4 · 2 · (1 + x/√2) · (1/√2)`; each factor is positive because `x > -√2`.
    unfold rhoQuad
    have hderiv : deriv (fun x : ℝ => Real.pi ^ 2 / 4 * (1 + x / Real.sqrt 2) ^ 2) x
        = Real.pi ^ 2 / 4 * (2 * (1 + x / Real.sqrt 2) * (1 / Real.sqrt 2)) := by
      simp
    rw [hderiv]
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : (0:ℝ) < 1 + x / Real.sqrt 2 := by
      have : (-1:ℝ) < x / Real.sqrt 2 := by
        rw [lt_div_iff₀ h2]; linarith
      linarith
    positivity

end Work.RPB.B5
