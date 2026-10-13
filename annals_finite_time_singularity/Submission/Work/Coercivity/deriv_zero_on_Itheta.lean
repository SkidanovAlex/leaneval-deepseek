import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- If `g` is differentiable at `θ`, vanishes at `θ`, and vanishes eventually along
`𝓝[s] θ` for a set `s` at which `θ` is a `UniqueDiffWithinAt` point, then `deriv g θ = 0`.

This is the one-sided core of `deriv_zero_on_Itheta`: the derivative of `g` at `θ` (with
respect to `𝓝 θ`) restricts to the within-derivative along `s`, and so does the derivative
of the constant function `0`, to which `g` is eventually equal along `𝓝[s] θ`; uniqueness
of the within-derivative gives the conclusion. -/
private theorem deriv_eq_zero_of_nhdsWithin {g : ℝ → ℝ} {θ : ℝ} {s : Set ℝ}
    (hd : DifferentiableAt ℝ g θ) (hu : UniqueDiffWithinAt ℝ s θ)
    (h0 : g θ = 0) (h : ∀ᶠ y in 𝓝[s] θ, g y = 0) : deriv g θ = 0 := by
  have h1 : HasDerivWithinAt g (deriv g θ) s θ := hd.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 s θ :=
    (hasDerivWithinAt_const θ s (0 : ℝ)).congr_of_eventuallyEq h h0
  have e1 : derivWithin g s θ = deriv g θ := h1.derivWithin hu
  have e2 : derivWithin g s θ = (0 : ℝ) := h2.derivWithin hu
  rw [e1] at e2
  exact e2

theorem deriv_zero_on_Itheta {g : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Spaces.Iθ)
    (hd : DifferentiableAt ℝ g θ) (h0 : ∀ θ' ∈ Spaces.Iθ, g θ' = 0) :
    deriv g θ = 0 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hgθ : g θ = 0 := h0 θ hθ
  rcases lt_or_eq_of_le hθ1 with hlt | heq
  · -- `θ < π/2`: `g` vanishes on the right-neighbourhood `(θ, π/2) ⊆ Iθ`.
    refine deriv_eq_zero_of_nhdsWithin hd (uniqueDiffWithinAt_Ioi θ) hgθ ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hlt] with y hy hygt
    exact h0 y ⟨le_trans hθ0 (le_of_lt hygt), le_of_lt hy⟩
  · -- `θ = π/2`: `g` vanishes on the left-neighbourhood `(0, θ) ⊆ Iθ`.
    refine deriv_eq_zero_of_nhdsWithin hd (uniqueDiffWithinAt_Iio θ) hgθ ?_
    have hpos : 0 < θ := by rw [heq]; linarith [Real.pi_pos]
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds hpos] with y hy hygt
    have hygt' : y < Real.pi / 2 := by simpa [heq] using hygt
    exact h0 y ⟨le_of_lt hy, le_of_lt hygt'⟩

end Work.Coercivity
