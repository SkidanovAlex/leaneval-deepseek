import Mathlib

namespace Work.HP.MM2

open scoped BigOperators

/-- Triangle inequality for `finsum` in `ℝ`: the absolute value of a finite sum of reals is at
most the sum of the absolute values (both sides being `0` when the support is infinite). -/
lemma abs_finsum_le {α : Type*} (f : α → ℝ) : |∑ᶠ p, f p| ≤ ∑ᶠ p, |f p| := by
  by_cases hf : (Function.support f).Finite
  · have hsub : Function.support (fun p => |f p|) = Function.support f := by
      ext x; simp [Function.mem_support, abs_eq_zero]
    have h1 : ∑ᶠ p, f p = ∑ p ∈ hf.toFinset, f p :=
      finsum_eq_sum_of_support_subset f (by rw [hf.coe_toFinset])
    have h2 : ∑ᶠ p, |f p| = ∑ p ∈ hf.toFinset, |f p| :=
      finsum_eq_sum_of_support_subset (fun p => |f p|) (by rw [hsub, hf.coe_toFinset])
    rw [h1, h2]
    exact Finset.abs_sum_le_sum_abs _ _
  · have h1 : ∑ᶠ p, f p = 0 := finsum_of_infinite_support hf
    have h2 : 0 ≤ ∑ᶠ p, |f p| := finsum_nonneg fun p => abs_nonneg _
    rw [h1, abs_zero]
    exact h2

theorem finsum_mem_abs_le {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ p ∈ S, f p| ≤ ∑ᶠ p ∈ S, |f p| := by
  rw [finsum_mem_def, finsum_mem_def]
  have h : S.indicator (fun p => |f p|) = fun p => |S.indicator f p| := by
    funext p
    by_cases hp : p ∈ S
    · simp [hp]
    · simp [hp]
  rw [h]
  exact abs_finsum_le _

end Work.HP.MM2
