import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-- The right walk `x ↦ (g ↦ avg_j x (g * B j))` sends mean-zero functions to mean-zero functions
(namespace `Work.LT`). -/
theorem lr_walk_mean_zero {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (b : G → ℝ)
    (hb : ∑ g, b g = 0) :
    ∑ g, ((∑ j : Fin Δ, b (g * B j)) / (Δ : ℝ)) = 0 := by
  rw [← Finset.sum_div]
  have h : (∑ g, ∑ j : Fin Δ, b (g * B j)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    exact (Equiv.sum_comp (Equiv.mulRight (B j)) b).trans hb
  rw [h, zero_div]

end Work.LT
