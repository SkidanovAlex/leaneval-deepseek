/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fundamental theorem of calculus for the square of a `z`-slice

For `F` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (`SmoothOpen F`), an interior
angle `θ ∈ (0,π/2)` and radii `0 < z₁ ≤ z₂`,

  `(F z₂ θ)^2 - (F z₁ θ)^2 = ∫_{z₁}^{z₂} 2 · F s θ · ∂_z F s θ ds`,

where `∂_z F = Work.Spaces.pz F` is the plain partial `z`-derivative of `F`.

This is the `z`-analogue of the classical one-dimensional FTC applied to the squared slice
`s ↦ (F s θ)^2`: its derivative is `2 F s θ · pz F s θ` by the chain rule
(`SmoothOpen.hasDerivAt_slice` + `HasDerivAt.pow`), and the integrand is continuous on the
compact interval `[z₁,z₂] ⊂ (0,∞)` hence interval integrable.  Resting on
`intervalIntegral.integral_eq_sub_of_hasDerivAt`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.ClassCHon.SliceMassAux

theorem slice_sq_ftc {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z₁ z₂ θ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (F z₂ θ) ^ 2 - (F z₁ θ) ^ 2
      = ∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ := by
  -- The interval of integration lies in the interior of the positive half-line.
  have hsub : Set.uIcc z₁ z₂ ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rw [Set.uIcc_of_le hz₁₂] at hs
    exact lt_of_lt_of_le hz₁ hs.1
  -- The integrand is continuous there (it is a product of `C^∞` slices of `F` and `pz F`).
  have hcont : ContinuousOn (fun s => 2 * F s θ * Work.Spaces.pz F s θ) (Set.uIcc z₁ z₂) :=
    ((continuousOn_const.mul (hF.curry_z hθ).continuousOn).mul
      (hF.pz.curry_z hθ).continuousOn).mono hsub
  have hint : IntervalIntegrable (fun s => 2 * F s θ * Work.Spaces.pz F s θ)
      MeasureTheory.volume z₁ z₂ :=
    hcont.intervalIntegrable
  -- Pointwise: the derivative of the squared slice is `2 F · ∂_z F`.
  have hderiv : ∀ s ∈ Set.uIcc z₁ z₂,
      HasDerivAt (fun s' : ℝ => (F s' θ) ^ 2) (2 * F s θ * Work.Spaces.pz F s θ) s := by
    intro s hs
    have hs0 : 0 < s := hsub hs
    have h := (hF.hasDerivAt_slice hθ hs0).pow 2
    convert h using 1
    ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm

end Work.FTS.ClassCHon.SliceMassAux
