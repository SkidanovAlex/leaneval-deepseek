/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `μ`-weighted angular slice at level `0`

This module proves the slice integrability

  `∀ z > 0, IntegrableOn (fun θ => g z θ ^ 2 * sin(2θ)^{2-γ(α)}) Iθ`

for `g ∈ ℋ^0` (`Work.Spaces.HkMem α 0 g`) which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen g`), with `γ(α) = 1 + α/10` and `α ≤ 1/4`.

The weight `sin(2θ)^{2-γ}` is *bounded* on `Iθ`: the exponent `2 - γ(α) = 1 - α/10` lies in
`[3/4, 1)`, so the whole estimate reduces to the integrability of the bare square `(g z θ)²`
on the slice.  That in turn is exactly the information carried by `HkMem α 0 g`, whose
level-`0` integrand is `(g z θ · w(z) / sin(2θ)^{η/2})²` with `η = 99/100 < 1`: since
`sin(2θ)^{η} ≤ 1` on `Iθ`, the radial weight is the only thing that changes, and dividing by
the nonzero constant `w(z)²` (`z > 0`) yields the `sEta`-weighted slice
(`Work.FTS.EllipticEst.remov.HkMem_zero_slice_Wt`), which dominates the bare square.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.bPairDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false

theorem HkMem_zero_slice_mu {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (h : Work.Spaces.HkMem α 0 g) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
  intro z hz
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (by positivity) (by positivity)
  -- Step 1: the `sEta`-weighted slice, from the level-`0` membership.
  have hEta : IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hWt := Work.FTS.EllipticEst.remov.HkMem_zero_slice_Wt h hzIz
    have hfac : (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.remov.Wt z θ)
        = fun θ => (Work.Spaces.w z) ^ 2
            * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      funext θ
      simp only [Work.FTS.EllipticEst.remov.Wt]
      ring
    rw [hfac] at hWt
    have h2 := hWt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => ?_)
      Work.FTS.EllipticEst.remov.measurableSet_Iθ
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]
  -- Step 2: restrict to the open angular interval (the endpoints are null).
  have hEta' : IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (π / 2)) :=
    hEta.mono_set (by intro θ hθ; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- Step 3: the `sin(2θ)`-factor is positive on the open interval.
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  -- Step 4: the target slice is continuous on the open interval.
  have hcont : ContinuousOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (π / 2)) := by
    have hg : ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo 0 (π / 2)) :=
      Work.FTS.LocData.continuousOn_slice_theta hsm.continuousOn hz
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    exact (hg.pow 2).mul (hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ))))
  -- Step 5: domination by the `sEta`-weighted slice on the open interval.
  have hmono : IntegrableOn
      (fun θ : ℝ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (π / 2)) := by
    refine MeasureTheory.Integrable.mono' hEta'
      (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hnn : 0 ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [Work.FTS.EllipticEst.sEta]
    refine Real.rpow_le_rpow_of_exponent_ge (hsinpos θ hθ) (Real.sin_le_one _) ?_
    simp only [Work.Spaces.gam, Work.Spaces.eta]
    nlinarith [hα, hα4]
  -- Step 6: transport back to the closed interval.
  refine MeasureTheory.IntegrableOn.congr_set_ae hmono ?_
  show Set.Icc 0 (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

end Work.FTS.ClassC.VopGen
