import Mathlib
import Submission.Work.RPB.B5.regDefs

open scoped ContDiff

set_option autoImplicit false

namespace Work.RPB.B5

/-- `Work.RPB.B5.pds hc τ t s` is the directional derivative of `hc` in the third coordinate,
written with `fderiv`; it coincides with the ordinary derivative `deriv (fun u => hc τ t u) s`.
(Helper for `Work.RPB.B5.regularizedPhaseIntegrand`; import `Submission.Work.RPB.B5.regDefs`.) -/
theorem pds_eq_deriv (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (τ t s : ℝ) :
    Work.RPB.B5.pds hc τ t s = deriv (fun u : ℝ => hc τ t u) s := by
  -- `pds` is the `fderiv` of `hc` at `(τ, (t, s))` applied to `(0, (0, 1))`, i.e. the derivative
  -- of the composition of `hc` with the curve `u ↦ (τ, (t, u))`, by the chain rule.
  have hF : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2)
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) (τ, (t, s))) (τ, (t, s)) :=
    ((hc_sm.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hφ : HasDerivAt (fun u : ℝ => (τ, (t, u))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) s :=
    (hasDerivAt_const (c := τ) s).prodMk
      ((hasDerivAt_const (c := t) s).prodMk (hasDerivAt_id s))
  have hcomp : HasDerivAt
      ((fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) ∘ fun u : ℝ => (τ, (t, u)))
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) (τ, (t, s))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) s :=
    hF.comp_hasDerivAt s hφ
  -- the composite is definitionally `u ↦ hc τ t u`
  have hcomp' : HasDerivAt (fun u : ℝ => hc τ t u)
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) (τ, (t, s))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) s := hcomp
  unfold Work.RPB.B5.pds
  exact hcomp'.deriv.symm

end Work.RPB.B5
