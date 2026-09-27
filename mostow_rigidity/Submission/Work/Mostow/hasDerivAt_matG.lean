import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

/-!
# Derivative of `matG`

`matG x = (1/2) * log x - log (1 - x)` on `(0, 1)`, with derivative
`matPhi x = 1/(2x) + 1/(1-x)`.
-/

namespace Work.Mostow

/-- On `(0,1)`, `matG` is differentiable with derivative `matPhi`. -/
theorem hasDerivAt_matG {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    HasDerivAt matG (matPhi a) a := by
  have hne : (1 - a) ≠ 0 := by linarith
  -- derivative of the first summand `(1/2) * log x`
  have h1d : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log x) ((1 / 2 : ℝ) * a⁻¹) a :=
    (Real.hasDerivAt_log (ne_of_gt h0)).const_mul (1 / 2 : ℝ)
  -- derivative of `log (1 - x)`
  have h2d : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1 : ℝ) / (1 - a)) a := by
    have hsub : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1 : ℝ) a :=
      (hasDerivAt_id a).const_sub (1 : ℝ)
    exact hsub.log hne
  have hsum : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log x - Real.log (1 - x))
      ((1 / 2 : ℝ) * a⁻¹ - ((-1 : ℝ) / (1 - a))) a := h1d.sub h2d
  have hval : (1 / 2 : ℝ) * a⁻¹ - ((-1 : ℝ) / (1 - a)) = matPhi a := by
    unfold matPhi
    rw [one_div, one_div]
    field_simp
    ring
  rw [hval] at hsum
  change HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log x - Real.log (1 - x)) (matPhi a) a
  exact hsum

end Work.Mostow
