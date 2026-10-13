/-
Copyright: work module for the Elgindi finite-time singularity project.

# Plancherel for the `t`-Fourier slice, second order

`Work.FTS.EllSol.FlatFT.plancherelDeriv2`:
`∫ ξ, (2πξ)⁴ ‖slice1 h ξ‖² = ∫ t, ‖deriv (deriv h) t‖²` for `h : ℝ → ℂ` of class `C²` with
compact support.

This is the second-order companion of
`Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv`.  Two ingredients:

* the pointwise derivative rule `slice1_deriv` of the sibling module, applied once to `h`
  (giving `slice1 (deriv h) ξ = 2πIξ · slice1 h ξ`) and once to `deriv h`
  (giving `slice1 (deriv (deriv h)) ξ = 2πIξ · slice1 (deriv h) ξ`);
* Plancherel for the first derivative, `plancherelSlice1Deriv (deriv h)`, whose right-hand
  side is literally `∫ t, ‖deriv (deriv h) t‖²`.

The two integrations by parts are not needed: the weight `(2πξ)⁴` is exactly the squared
modulus of `(2πIξ)²`, so the identity follows pointwise in `ξ` (this is
`norm_sq_mul_two_pi_I`, used twice).

The relevant smoothness/compact-support bookkeeping is the Mathlib API
`ContDiff.deriv'` (`hh.deriv' : ContDiff ℝ 1 (deriv h)` from `hh : ContDiff ℝ 2 h`),
`ContDiff.of_le` and `HasCompactSupport.deriv`.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllSol.FlatFT

/-- **Plancherel's theorem for the second `t`-Fourier derivative.**  For `h : ℝ → ℂ` of class
`C²` with compact support, the weighted `L²` norm of the Fourier slice against the weight
`(2πξ)⁴` equals the `L²` norm of the second derivative `deriv (deriv h)`. -/
theorem plancherelDeriv2 (h : ℝ → ℂ) (hh : ContDiff ℝ 2 h) (hs : HasCompactSupport h) :
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 4 * ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv (deriv h) t‖ ^ 2 := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have h2 : ContDiff ℝ 1 (deriv h) := hh.deriv'
  have h3 : HasCompactSupport (deriv h) := hs.deriv
  rw [← plancherelSlice1Deriv (deriv h) h2 h3]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [slice1_deriv h h1 hs ξ, norm_sq_mul_two_pi_I]
  ring

end Work.FTS.EllSol.FlatFT
