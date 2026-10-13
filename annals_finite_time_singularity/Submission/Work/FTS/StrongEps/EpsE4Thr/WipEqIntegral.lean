/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/WipEqIntegral.lean` — identifying `wip` with the product
measure integral

`Work.Coercivity.wip ρ A B = ∫_{z ∈ Iz} ∫_{θ ∈ Iθ} A(z,θ)·B(z,θ)·ρ(z,θ)` is an *iterated*
set-integral, while the energy identities produced by `hasDerivAt_integral_diag_var` are about
`∫ p, A p.1 p.2 * B p.1 p.2 * ρ p.1 p.2 ∂μ` for the product measure

  `mup = (volume.restrict Iz).prod (volume.restrict Iθ)`.

The bridge is Fubini (`MeasureTheory.integral_integral`), available as soon as the integrand is
`μ`-integrable.  `mup` is also the measure against which all the `ℋ`-integrability and
strong-measurability hypotheses of this chapter are stated.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.EnergyStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false

/-- The product measure `(volume.restrict I_z).prod (volume.restrict I_θ)` against which the slot
integrability and measurability of this chapter are stated. -/
def mup : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- **`wip` is the product-measure integral** of the pairing integrand, whenever that integrand is
integrable. -/
theorem wip_eq_integral_prod {ρ A B : ℝ → ℝ → ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 p.2 * B p.1 p.2 * ρ p.1 p.2) mup) :
    Work.Coercivity.wip ρ A B
      = ∫ p : ℝ × ℝ, A p.1 p.2 * B p.1 p.2 * ρ p.1 p.2 ∂mup := by
  rw [Work.Coercivity.wip, mup]
  exact MeasureTheory.integral_integral
    (f := fun z θ => A z θ * B z θ * ρ z θ) h

/-- The diagonal case: `wip ρ A A = ∫ p, A p.1 p.2 * A p.1 p.2 * ρ p.1 p.2` — the form in which
the `L²`-route derivative (`hasDerivAt_integral_diag_var`) states its conclusion. -/
theorem wip_self_eq_integral_prod {ρ A : ℝ → ℝ → ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 p.2 * A p.1 p.2 * ρ p.1 p.2) mup) :
    Work.Coercivity.wip ρ A A
      = ∫ p : ℝ × ℝ, A p.1 p.2 * A p.1 p.2 * ρ p.1 p.2 ∂mup :=
  wip_eq_integral_prod h

/-- The squared spelling of `wip_self_eq_integral_prod`. -/
theorem wip_self_eq_integral_prod_sq {ρ A : ℝ → ℝ → ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2 * ρ p.1 p.2) mup) :
    Work.Coercivity.wip ρ A A
      = ∫ p : ℝ × ℝ, (A p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup := by
  have h' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 p.2 * A p.1 p.2 * ρ p.1 p.2) mup := by
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [wip_self_eq_integral_prod h']
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)

end Work.FTS.StrongEps.EpsE4Thr
