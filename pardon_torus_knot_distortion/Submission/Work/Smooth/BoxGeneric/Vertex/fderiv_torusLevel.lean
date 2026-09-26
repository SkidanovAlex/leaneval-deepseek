import Mathlib
import Submission.Work.Core.Torus

namespace Work.Smooth.BoxGeneric.Vertex

open LeanEval.KnotTheory.PardonDistortion

/-- The derivative of the level function of the standard torus of revolution,
`y ↦ (‖y‖² + 3)² - 16 (y₀² + y₁²)`, evaluated at `z`.

The function is a composition of the coordinate projections `y ↦ yᵢ` (whose
derivative is `PiLp.proj 2 _ i`) with the polynomial
`(u₀² + u₁² + u₂² + 3)² - 16 (u₀² + u₁²)`, and the claim is exactly the chain
rule evaluated in the coordinates. -/
theorem fderiv_torusLevel (y z : LeanEval.KnotTheory.PardonDistortion.R3) :
    fderiv ℝ (fun y : LeanEval.KnotTheory.PardonDistortion.R3 =>
        (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2)) y z
      = 4 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) * (y 0 * z 0 + y 1 * z 1 + y 2 * z 2)
        - 32 * (y 0 * z 0 + y 1 * z 1) := by
  -- Derivative of the coordinate functions `y ↦ yᵢ`.
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y (0 : Fin 3)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y (1 : Fin 3)
  have h2 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y (2 : Fin 3)
  -- Derivative of `y ↦ y₀² + y₁² + y₂² + 3`.
  have hS := (((h0.pow 2).add (h1.pow 2)).add (h2.pow 2)).add (hasFDerivAt_const (3 : ℝ) y)
  -- Derivative of `y ↦ y₀² + y₁²`.
  have hQ := (h0.pow 2).add (h1.pow 2)
  -- Derivative of the full level function.
  have hF : HasFDerivAt (fun x : R3 =>
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + 3) ^ 2 - 16 * (x 0 ^ 2 + x 1 ^ 2)) _ y :=
    (hS.pow 2).sub (hQ.const_mul 16)
  -- Evaluation of the coordinate projections.
  have hproj : ∀ (i : Fin 3) (w : R3),
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : R3 →L[ℝ] ℝ) w = w i :=
    fun i w => rfl
  rw [hF.fderiv]
  simp only [sub_apply, add_apply, smul_apply, zero_apply, hproj, Pi.add_apply]
  ring

end Work.Smooth.BoxGeneric.Vertex
