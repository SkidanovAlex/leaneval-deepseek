/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkSq α 0 g` as the `z`-integral of the `θ`-slice of the weighted square

This module identifies the level-`0` `H^k`-quantity of `g` with the iterated integral in which
the radial factor `w2 z = w z ^ 2` sits *outside* the angular integration:

  `HkSq α 0 g = ∫_z w2 z · (∫_θ g z θ ^ 2 · σ θ)`.

`Work.Spaces.HkSq α 0 g` is by definition `∫_z ∫_θ HkIntegrand α 0 g z θ`, and at level `0` the
integrand is the single square `(g z θ · w z / sin(2θ)^{η/2})²`
(`HkIntegrand_zero_eq`), which equals `g z θ · g z θ · w2 z · σ θ` pointwise
(`AngSecond.sq_mul_W`).  Since `w2 z` does not depend on `θ`, the constant factor can be pulled
out of, or pushed into, the angular integral (`MeasureTheory.integral_const_mul`), which gives
the identity above.  The *integrability* half of the statement transfers from
`HkMem α 0 g` by `MeasureTheory.IntegrableOn.congr_fun`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- **The slice identity.**  For every `z`, the radial weight `w2 z` times the angular
integral `∫_θ g z θ ^ 2 · σ θ` is the angular integral of the level-`0` `HkIntegrand`. -/
theorem w2_mul_slice_eq_HkIntegrand_slice (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ := by
  -- Push the constant `w2 z` into the angular integral, using `sq_mul_W` pointwise.
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.w2 z
            * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [HkIntegrand_zero_eq, AngSecond.sq_mul_W g hθ]
    ring
  have h2 : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.AngSecond.w2 z
          * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    MeasureTheory.integral_const_mul _ _
  exact h2.symm.trans h1.symm

theorem hksq_eq_w2_sliceIntegral {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn
        (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
          * ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        Work.Spaces.Iz
      ∧ ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AngSecond.w2 z
            * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        = Work.Spaces.HkSq α 0 g := by
  have hslice : ∀ z : ℝ,
      Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
    fun z => w2_mul_slice_eq_HkIntegrand_slice α g z
  constructor
  · -- Integrability transfers from `HkMem α 0 g` along the pointwise slice identity.
    exact MeasureTheory.IntegrableOn.congr_fun hg.2
      (fun z _ => (hslice z).symm) measurableSet_Ici
  · rw [Work.Spaces.HkSq]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hslice z)

end Work.FTS.EllipticEst.Honest
