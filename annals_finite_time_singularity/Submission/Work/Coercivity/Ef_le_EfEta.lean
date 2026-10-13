import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.L2CoercivityTransport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- `Ef f ≤ EfEta f`: the `sin(2θ)^{-η}` angular weight is `≥ 1` almost everywhere on
the quadrant (`η = 99/100`, and `sin(2θ) ≤ 1` there), so the `η`-weighted `L²` norm
dominates the unweighted one. -/
theorem Ef_le_EfEta (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    Ef f ≤ EfEta f := by
  set P : Measure (ℝ × ℝ) :=
    (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  -- ## Integrability of the two integrands against the product measure
  have hIntEf : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h := integrableOn_prod (f_sq_w_sq_integrable α f hi)
    refine h.congr (Eventually.of_forall fun p => ?_)
    ring
  have hIntEfEta : Integrable (fun p : ℝ × ℝ =>
      (f p.1 p.2 * Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
    have h := integrableOn_prod (g := fun z θ =>
      f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) hi.intFeta
    refine h.congr (Eventually.of_forall fun p => ?_)
    ring
  -- ## The two energies as integrals against the product measure
  have hEf : (∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) = Ef f := by
    rw [hP, Ef_eq_wip,
      wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) f f
        (by simpa using f_sq_w_sq_integrable α f hi)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  have hEfEta : (∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂P) = EfEta f := by
    rw [hP, EfEta_eq_wip,
      wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        f f (by
          have hfun : (fun z θ => f z θ * f z θ
                * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
              = (fun z θ => f z θ * f z θ * Spaces.w z ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
            funext z θ; ring
          rw [hfun]
          exact hi.intFeta)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  -- ## The pointwise (a.e.) inequality
  have hle : ∀ᵐ p ∂P, (f p.1 p.2 * Spaces.w p.1) ^ 2
      ≤ (f p.1 p.2 * Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta) := by
    have hquad : ∀ᵐ p ∂P, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := ae_prod_quadrant
    have hne : ∀ᵐ p ∂P, Real.sin (2 * p.2) ≠ 0 := by
      rw [hP, ← volume_restrict_prod]
      exact ae_restrict_of_ae ae_sin_two_ne_zero
    filter_upwards [hquad, hne] with p hp hsin
    simpa using mul_le_mul_of_nonneg_left ((sin_two_eta_facts (z := p.1) f hp.2 hsin).1)
      (sq_nonneg (f p.1 p.2 * Spaces.w p.1))
  -- ## Assembly
  calc Ef f = ∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P := hEf.symm
    _ ≤ ∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂P :=
        integral_mono_ae hIntEf hIntEfEta hle
    _ = EfEta f := hEfEta

end Work.Coercivity
