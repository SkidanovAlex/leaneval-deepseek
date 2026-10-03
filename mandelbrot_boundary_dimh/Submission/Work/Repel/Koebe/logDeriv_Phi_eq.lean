import Mathlib
import Submission.Work.Repel.Koebe.ExteriorWindingDefs

/-!
# The logarithmic derivative of `Φ`

On the punctured disc `Phi g ζ` agrees with `v ↦ v * (g v⁻¹ - ζ)`, so at `v ≠ 0` its logarithmic
derivative is

`logDeriv (Phi g ζ) v = 1 / v - (v ^ 2)⁻¹ * (deriv g v⁻¹ / (g v⁻¹ - ζ))`,

the first term coming from the factor `v` and the second from the chain rule applied to `g v⁻¹`
(the derivative of `w ↦ w⁻¹` at `v` being `-(v ^ 2)⁻¹`).
-/

open Filter Topology
open scoped Topology

namespace Work.Repel.Koebe

theorem logDeriv_Phi_eq {g : ℂ → ℂ} {ζ v : ℂ} (hv : v ≠ 0) (hgv : AnalyticAt ℂ g v⁻¹)
    (hne : g v⁻¹ ≠ ζ) :
    logDeriv (Phi g ζ) v = 1 / v - (v ^ 2)⁻¹ * (deriv g v⁻¹ / (g v⁻¹ - ζ)) := by
  have hdg : DifferentiableAt ℂ g v⁻¹ := hgv.differentiableAt
  have hdiv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) v := differentiableAt_inv hv
  -- `Phi g ζ` agrees with `w ↦ w * (g w⁻¹ - ζ)` near the nonzero point `v`
  have heq : Phi g ζ =ᶠ[𝓝 v] fun w => w * (g w⁻¹ - ζ) := by
    filter_upwards [isOpen_ne.mem_nhds hv] with w hw
    exact Phi_apply g ζ hw
  have hlog : logDeriv (Phi g ζ) v = logDeriv (fun w => w * (g w⁻¹ - ζ)) v :=
    (logDeriv_congr_nhds heq).self_of_nhds
  rw [hlog]
  have hsub : DifferentiableAt ℂ (fun w : ℂ => g w⁻¹ - ζ) v :=
    (hdg.comp v hdiv).sub (differentiableAt_const ζ)
  -- product rule for the logarithmic derivative
  have hmul : logDeriv (fun w => w * (g w⁻¹ - ζ)) v
      = logDeriv id v + logDeriv (fun w : ℂ => g w⁻¹ - ζ) v :=
    logDeriv_mul (f := id) (g := fun w : ℂ => g w⁻¹ - ζ) v (by simpa using hv)
      (sub_ne_zero.mpr hne) differentiableAt_id hsub
  rw [hmul, logDeriv_id]
  -- chain rule: `deriv (fun w => g w⁻¹) v = deriv g v⁻¹ * (-(v ^ 2)⁻¹)`
  have hderiv : deriv (fun w : ℂ => g w⁻¹ - ζ) v = deriv g v⁻¹ * (-(v ^ 2)⁻¹) := by
    have h1 : HasDerivAt (fun w : ℂ => g w⁻¹) (deriv g v⁻¹ * deriv (fun w : ℂ => w⁻¹) v) v :=
      (hdg.hasDerivAt).comp v hdiv.hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => g w⁻¹ - ζ)
        (deriv g v⁻¹ * deriv (fun w : ℂ => w⁻¹) v) v :=
      h1.sub_const ζ
    rw [h2.deriv, deriv_inv]
  rw [logDeriv_apply, hderiv]
  ring

end Work.Repel.Koebe
