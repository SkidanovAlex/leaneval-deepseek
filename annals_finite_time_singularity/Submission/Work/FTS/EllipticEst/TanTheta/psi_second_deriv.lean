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

namespace Work.FTS.EllipticEst.TanTheta

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedSimpArgs false

/-- **The chain rule for `u = cos θ · ψ`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `u''(θ) = ψ''(θ)·cos θ - 2·ψ'(θ)·sin θ - ψ(θ)·cos θ`.

Route: near `θ` the identity `u = ψ · cos` holds (as `cos ≠ 0`), so `u' = ψ'·cos - ψ·sin` as
functions near `θ`; differentiating that exhibited expression at `θ` (product rule, for which
`ψ'` must be differentiable at `θ`, which follows from `ψ` being `C²` there since it is the
quotient of the `C²` function `u` by the nonvanishing smooth function `cos`) gives the claim. -/
private lemma deriv_deriv_eq_div_cos (u : ℝ → ℝ) {θ : ℝ}
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

/-- The second derivative of `ψ = u / cos` satisfies, on `(0, π/2)`,
`cos θ · ψ'' θ = u'' θ + cos θ · ψ θ + 2 sin θ · ψ' θ`
(this is the rearrangement of `u'' = -cos θ ψ - 2 sin θ ψ' + cos θ ψ''`).

Route: on `(0, π/2)` one has `u = cos · ψ` (since `cos θ ≠ 0`), so the second derivative of
`θ ↦ Real.cos θ * psi u θ` equals `deriv (deriv u)`; expand that second derivative with the
product rule twice (`HasDerivAt.mul`, `.congr_of_eventuallyEq` to move between `u` and
`cos * ψ`, `.deriv`) and use `psi_deriv_formula` for `ψ'` (or redo the quotient rule). -/
theorem psi_second_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * deriv (deriv (Work.FTS.EllipticEst.TanTheta.psi u)) θ
      = deriv (deriv u) θ + Real.cos θ * Work.FTS.EllipticEst.TanTheta.psi u θ
        + 2 * Real.sin θ * deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ := by
  have hθI : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have huAt : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
  have h := deriv_deriv_eq_div_cos u huAt hc
  change Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
        + 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ
  rw [h]
  ring

end Work.FTS.EllipticEst.TanTheta
