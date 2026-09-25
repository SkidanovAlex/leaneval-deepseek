import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators

namespace Commons.Algebra.BigOperators

theorem card_le_finsum_of_one_le {α : Type*} {g : α → ℝ} (hnn : ∀ x, 0 ≤ g x)
    (hfin : Function.HasFiniteSupport g) (A : Finset α) (hA : ∀ x ∈ A, 1 ≤ g x) :
    (A.card : ℝ) ≤ ∑ᶠ x, g x := by
  classical
  have hsubA : A ⊆ hfin.toFinset := fun x hx =>
    hfin.mem_toFinset.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (hA x hx)))
  have hsupp : Function.support g ⊆ (hfin.toFinset : Set α) := fun x hx =>
    hfin.mem_toFinset.mpr hx
  rw [finsum_eq_sum_of_support_subset g hsupp]
  calc (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ A, g x := Finset.sum_le_sum fun x hx => hA x hx
    _ ≤ ∑ x ∈ hfin.toFinset, g x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubA fun x _ _ => hnn x

end Commons.Algebra.BigOperators