import Submission.Work.EKLC6Core.famIndicator

/-!
# `Work.EKLC6Core.famIndicatorSum`

Elementary rewriting and pointwise bounds for `Work.EKLC6Core.famIndicator`.

These are shared between `Work.EKLC6Core.exists_famIndicator_approx` and the
lemmas it is assembled from, so they live in their own module.
-/

open MeasureTheory

namespace Work.EKLC6Core

/-- `famIndicator S c` may be written as a sum over any finset containing the support of `c`. -/
theorem famIndicator_eq_sum_of_support_subset {X : Type*} (S : ℕ → Set X) (c : ℕ →₀ ℚ)
    (t : Finset ℕ) (ht : c.support ⊆ t) :
    famIndicator S c
      = fun x => ∑ n ∈ t, ((c n : ℚ) : ℝ) * (S n).indicator (fun _ => (1 : ℝ)) x := by
  funext x
  rw [famIndicator_apply]
  refine Finset.sum_subset ht ?_
  intro n _ hn
  rw [Finsupp.notMem_support_iff.mp hn]
  simp

/-- The `ℓ¹` coefficient norm of a `famIndicator` combination, over any finset containing the
support. -/
theorem sum_abs_famIndicator_eq {X : Type*} (_S : ℕ → Set X) (c : ℕ →₀ ℚ) (t : Finset ℕ)
    (ht : c.support ⊆ t) :
    (∑ n ∈ t, |((c n : ℚ) : ℝ)|) = ∑ n ∈ c.support, |((c n : ℚ) : ℝ)| := by
  rw [Finset.sum_subset ht (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]

/-- Pointwise comparison of a real combination with the `famIndicator` of a rational
combination whose support is contained in the index set. -/
theorem abs_sub_famIndicator_le {X : Type*} (S : ℕ → Set X) (ι : Finset ℕ)
    (c : ℕ → ℝ) (q : ℕ →₀ ℚ) (hq : q.support ⊆ ι) (x : X) :
    |(∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x) - famIndicator S q x|
      ≤ ∑ n ∈ ι, |c n - (q n : ℝ)| := by
  have hqeq := famIndicator_eq_sum_of_support_subset S q ι hq
  rw [hqeq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun n hn => ?_
  rw [← sub_mul]
  have h : |(S n).indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ S n
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  calc |(c n - (q n : ℝ)) * (S n).indicator (fun _ => (1 : ℝ)) x|
      = |c n - (q n : ℝ)| * |(S n).indicator (fun _ => (1 : ℝ)) x| := by rw [abs_mul]
    _ ≤ |c n - (q n : ℝ)| * 1 := by
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |c n - (q n : ℝ)| := mul_one _

end Work.EKLC6Core
