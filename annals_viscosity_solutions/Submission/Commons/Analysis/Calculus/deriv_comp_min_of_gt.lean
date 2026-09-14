import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Calculus

/-- The derivative of `t ↦ γ (min t τ)` strictly to the right of `τ` vanishes. -/
theorem deriv_comp_min_of_gt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : ℝ → F) {τ t : ℝ} (ht : τ < t) :
    deriv (fun s : ℝ => γ (min s τ)) t = 0 := by
  have h : (fun s : ℝ => γ (min s τ)) =ᶠ[nhds t] fun _ => γ τ := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact congrArg γ (min_eq_right (le_of_lt hs))
  rw [h.deriv_eq, deriv_const]

end Commons.Analysis.Calculus