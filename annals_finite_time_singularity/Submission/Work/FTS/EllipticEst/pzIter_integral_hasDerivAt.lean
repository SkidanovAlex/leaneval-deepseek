/-
Copyright: work module for the Elgindi finite-time singularity project.

# Differentiation under the `θ`-integral for the iterated `z`-derivatives `pzIter`

For `u` smooth on a neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and `φ`
continuous on `Iθ = [0,π/2]`, the parametric integral

  `s ↦ ∫_θ (∂_z^k u)(s,θ) · φ(θ) dθ`

is differentiable on `(-1,∞)`, with derivative the integral of the next `z`-derivative:

  `∫_θ (∂_z^{k+1} u)(s,θ) · φ(θ) dθ`.

This is the Leibniz rule for the iterated derivative `pzIter`; it is the step that turns the
`H^k` energy estimates of §7 of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887

into statements about the next level of derivatives.  The general machinery is
`Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt`; here it is instantiated on the
full range `(-1,∞)` of the radial parameter, using that `(-1,∞) × Iθ` is contained in the
open set `U` on which `u` is smooth (`Work.Spaces.SmoothNbhd`).

## Main result

* `pzIter_integral_hasDerivAt` : the derivative of `∫_θ pzIter k u s θ · φ θ dθ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Joint continuity of the integrand on `(-1,∞) × Iθ` -/

/-- The integrand `(s,θ) ↦ (∂_z^k u)(s,θ) · φ(θ)` is jointly continuous on
`(-1,∞) × Iθ`, because `(-1,∞) × Iθ` is contained in the open set `U` on which the
`SmoothNbhd` function `u` is smooth and `φ` is continuous on `Iθ`. -/
theorem continuousOn_uncurry_pzIter_mul (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k u p.1 p.2 * φ p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
  have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
    Work.Spaces.smoothNbhd_pzIter hu k
  have hsub : Set.Ioi (-1 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
    Set.prod_mono subset_rfl fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 : ContinuousOn (Function.uncurry (Work.Spaces.pzIter k u))
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := (hsm.mono hsub).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => φ p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    hφ.comp continuousOn_snd fun p hp => hp.2
  exact (h1.mul h2).congr fun p _ => rfl

/-! ## The main theorem -/

theorem pzIter_integral_hasDerivAt (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioi (-1)) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) u s θ * φ θ) s := by
  refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
    (g := fun s θ => Work.Spaces.pzIter k u s θ * φ θ)
    (g' := fun s θ => Work.Spaces.pzIter (k + 1) u s θ * φ θ)
    isOpen_Ioi hs ?_ ?_ ?_
  · exact continuousOn_uncurry_pzIter_mul u φ hu hφ k
  · exact continuousOn_uncurry_pzIter_mul u φ hu hφ (k + 1)
  · intro θ hθ s' hs'
    have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
      Work.Spaces.smoothNbhd_pzIter hu k
    have h := (Work.Spaces.hardyZ_hasDerivAt_slice (Work.Spaces.pzIter k u) hsm hθ hs').mul_const
      (φ θ)
    simpa [Work.Spaces.pzIter_succ] using h

end Work.FTS.EllipticEst
