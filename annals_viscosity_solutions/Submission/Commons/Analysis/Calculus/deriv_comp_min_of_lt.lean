import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Calculus

open Filter
open scoped Topology

/-- The derivative of `t ↦ γ (min t τ)` strictly to the left of `τ` is the derivative of `γ`. -/
theorem deriv_comp_min_of_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : ℝ → F) {τ t : ℝ} (ht : t < τ) :
    deriv (fun s : ℝ => γ (min s τ)) t = deriv γ t := by
  have h : (fun s : ℝ => γ (min s τ)) =ᶠ[𝓝 t] γ := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    rw [Set.mem_Iio] at hs
    simp [min_eq_left hs.le]
  exact h.deriv_eq

end Commons.Analysis.Calculus