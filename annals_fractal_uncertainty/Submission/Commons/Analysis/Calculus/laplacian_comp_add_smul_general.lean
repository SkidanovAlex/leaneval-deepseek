import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Submission.Commons.Analysis.Calculus.laplacian_comp_add_smul

namespace Commons.Analysis.Calculus

/-- **The Laplacian along a complex line, for an arbitrary complex normed space.**

Let `E` be a complex normed space (viewed as a real normed space), `u : E → ℝ` be `C²` at `z ∈ E`,
and `v ∈ E`.  Then the Laplacian at `0` of the function `ζ ↦ u (z + ζ • v)` of the complex variable
`ζ` is the sum of the second derivatives of `u` at `z` in the two directions `v` and `I • v`:

`Δ (ζ ↦ u (z + ζ • v)) 0 = D²u(z)[v, v] + D²u(z)[I • v, I • v]`.

This is the generalisation of `laplacian_comp_add_smul` from `EuclideanSpace ℂ (Fin d)` to an
arbitrary complex normed space `E`.  The proof is the same: parametrising `ℂ` by its real orthonormal
basis `1, I` turns the Laplacian on `ℂ` into the sum of the two second derivatives along `1` and `I`,
and the second-order chain rule `iteratedFDeriv_two_comp_add_clm` pulls these back along the
continuous linear map `ζ ↦ ζ • v`. -/
theorem laplacian_comp_add_smul_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → ℝ} {z v : E} (hu : ContDiffAt ℝ 2 u z) :
    Laplacian.laplacian (fun ζ : ℂ => u (z + ζ • v)) 0 =
      (iteratedFDeriv ℝ 2 u z) ![v, v]
        + (iteratedFDeriv ℝ 2 u z) ![Complex.I • v, Complex.I • v] := by
  -- `ζ ↦ ζ • v` is a continuous linear map `ℂ →L[ℝ] E`.
  set L : ℂ →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ (E := E) ℂ).flip v with hL
  have hψ : (fun ζ : ℂ => u (z + ζ • v)) = fun ζ : ℂ => u (z + L ζ) := by
    funext ζ
    simp only [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
  rw [hψ, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  -- the two second derivatives along the real orthonormal basis `1, I` of `ℂ`
  rw [iteratedFDeriv_two_comp_add_clm hu L (1 : ℂ),
      iteratedFDeriv_two_comp_add_clm hu L Complex.I]
  simp [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]

end Commons.Analysis.Calculus