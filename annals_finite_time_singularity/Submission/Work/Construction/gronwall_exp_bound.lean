import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

/-- Gronwall-type exponential bound: if `φ` is continuous on `[0,∞)`, differentiable on
`(0,∞)` with `φ' ≤ -b φ` there, and `φ 0 ≤ K`, then `φ τ ≤ K e^{-b τ}` for every `τ ≥ 0`.

The argument multiplies through by the integrating factor `e^{b τ}`: the function
`g τ = φ τ e^{b τ}` has derivative `(φ' τ + b φ τ) e^{b τ} ≤ 0` on `(0,∞)`, hence is
antitone on `[0,∞)`; so `φ τ e^{b τ} ≤ φ 0 ≤ K`. -/
theorem gronwall_exp_bound {φ : ℝ → ℝ} {b K : ℝ} (hb : 0 < b)
    (hcont : ContinuousOn φ (Set.Ici 0))
    (hdiff : ∀ τ, 0 < τ → HasDerivAt φ (deriv φ τ) τ)
    (hline : ∀ τ, 0 < τ → deriv φ τ ≤ -b * φ τ)
    (h0 : φ 0 ≤ K) :
    ∀ τ, 0 ≤ τ → φ τ ≤ K * Real.exp (-(b * τ)) := by
  have _hb : 0 < b := hb
  set g : ℝ → ℝ := fun τ => φ τ * Real.exp (b * τ) with hg
  -- derivative of the exponential factor `τ ↦ e^{b τ}`
  have he : ∀ τ, HasDerivAt (fun τ => Real.exp (b * τ)) (b * Real.exp (b * τ)) τ := by
    intro τ
    have h := (hasDerivAt_const_mul (x := τ) b).exp
    simpa [mul_comm] using h
  -- derivative of `g`
  have hgd : ∀ τ, 0 < τ → HasDerivAt g ((deriv φ τ + b * φ τ) * Real.exp (b * τ)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ => φ τ * Real.exp (b * τ))
        (deriv φ τ * Real.exp (b * τ) + φ τ * (b * Real.exp (b * τ))) τ :=
      (hdiff τ hτ).mul (he τ)
    rw [hg]
    convert h1 using 1
    ring
  have hg_cont : ContinuousOn g (Set.Ici 0) := by
    rw [hg]; exact hcont.mul (by fun_prop)
  have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    intro τ hτ
    exact (hgd τ hτ).differentiableAt.differentiableWithinAt
  have hgd_nonpos : ∀ x ∈ interior (Set.Ici 0), deriv g x ≤ 0 := by
    rw [interior_Ici]
    intro τ hτ
    rw [(hgd τ hτ).deriv]
    have hle : deriv φ τ + b * φ τ ≤ 0 := by
      have := hline τ hτ; linarith
    exact mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  -- `g` is antitone on `[0,∞)`
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici 0) hg_cont hg_diff hgd_nonpos
  intro τ hτ
  have hle : φ τ * Real.exp (b * τ) ≤ φ 0 := by
    have := hanti (by simp) (by simpa using hτ) hτ
    simpa [hg] using this
  have h1 : φ τ = (φ τ * Real.exp (b * τ)) * Real.exp (-(b * τ)) := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  calc φ τ = (φ τ * Real.exp (b * τ)) * Real.exp (-(b * τ)) := h1
    _ ≤ φ 0 * Real.exp (-(b * τ)) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ ≤ K * Real.exp (-(b * τ)) := mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le

end Work.Construction
