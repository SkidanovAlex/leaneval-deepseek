/-
Copyright: work module for the Elgindi finite-time singularity project.

# The chain rule for `u = cos θ · ψ`, in the honest (open-interval) class

If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with `ψ = u / cos` one has
`u''(θ) = ψ''(θ)·cos θ - 2·ψ'(θ)·sin θ - ψ(θ)·cos θ`, equivalently
`cos θ · ψ''(θ) = u''(θ) + cos θ · ψ(θ) + 2 sin θ · ψ'(θ)`.

This is the pointwise input of the `I₄`-identity
`Work.FTS.EllipticEst.Honest.slice_ident_honest`: it is what lets one eliminate the second
derivative `ψ''` of the slice variable from the weighted products `ρ ψ' ψ''`
(`ρ = sin θ cos θ · sin(2θ)^{-η}`), whose integrability is not a hypothesis of the honest
slice estimate.

The first statement is the de-privatised form of
`Work.FTS.EllipticEst.TanTheta.deriv_deriv_eq_div_cos`
(`Submission/Work/FTS/EllipticEst/TanTheta/psi_second_deriv.lean`), with the *neighbourhood*
smoothness hypothesis of that file (`ContDiffOn ℝ 2 u (Ioo (-1) (π/2+1))`) replaced by
smoothness at the single point.  Nothing here contains a `sorry`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.TanTheta.Basic

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
set_option linter.unusedSimpArgs false

/-- **The chain rule for `u = cos θ · ψ`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `u''(θ) = ψ''(θ)·cos θ - 2·ψ'(θ)·sin θ - ψ(θ)·cos θ`.

Route: near `θ` the identity `u = ψ · cos` holds (as `cos ≠ 0`), so `u' = ψ'·cos - ψ·sin` as
functions near `θ`; differentiating that exhibited expression at `θ` (product rule, for which
`ψ'` must be differentiable at `θ`, which follows from `ψ` being `C²` there since it is the
quotient of the `C²` function `u` by the nonvanishing smooth function `cos`) gives the claim. -/
theorem derivDeriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  -- `u' = ψ' · cos - ψ · sin`, as an eventual equality of functions
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  -- the two factors of the exhibited expression are differentiable at `θ`
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-- **The rearranged chain rule.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `cos θ · ψ''(θ) = u''(θ) + cos θ · ψ(θ) + 2 sin θ · ψ'(θ)`.

This is the form in which the second derivative `ψ''` of the slice variable is eliminated
from the products of the `I₄` calculus: multiplying by `sin θ · sin(2θ)^{-η} · ψ'(θ)` turns
`sin θ cos θ sin(2θ)^{-η} ψ' ψ''` into a combination of the (given) integrable quantities
`sin²θ sin(2θ)^{-η} (ψ')²`, `sin θ sin(2θ)^{-η} ψ' u''` and `sin θ cos θ sin(2θ)^{-η} ψ ψ'`. -/
theorem cos_mul_derivDeriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
        + 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ := by
  have h := derivDeriv_divCos u hu hcos
  linarith [h]

end Work.FTS.EllipticEst.Honest
