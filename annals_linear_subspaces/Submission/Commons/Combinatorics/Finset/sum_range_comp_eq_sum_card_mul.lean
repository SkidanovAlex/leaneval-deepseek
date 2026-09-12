import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Finset

theorem sum_range_comp_eq_sum_card_mul {ℓ R : ℕ} {n : ℕ → ℕ} (hn : ∀ j < ℓ, n j < R) (phi : ℕ → ℝ) :
    ∑ j ∈ Finset.range ℓ, phi (n j) =
      ∑ s ∈ Finset.range R, (((Finset.range ℓ).filter (fun j => n j = s)).card : ℝ) * phi s := by
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := Finset.range ℓ) (t := Finset.range R) (g := n) (f := phi)]
  · apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_const, nsmul_eq_mul]
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact hn i hi

end Commons.Combinatorics.Finset