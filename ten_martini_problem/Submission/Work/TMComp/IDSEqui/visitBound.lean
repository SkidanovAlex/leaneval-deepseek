import Mathlib
import Submission.Work.TMComp.IDSDefs

namespace Work.TMComp.IDSEqui

/-- If `f ≤ 1` pointwise and `f` vanishes where `fracDist ≥ δ`, then the sum of `f` over the
first `n` points of the orbit `θ + jα` is at most the number of those points lying within
distance `δ` of the integers.  (The summands outside that set contribute `0`, and inside it
they contribute at most `1`.) -/
theorem visitBound (α θ δ : ℝ) (n : ℕ) (f : ℝ → ℝ)
    (h1 : ∀ x, f x ≤ 1) (h2 : ∀ x, δ ≤ Work.TMContract.fracDist x → f x = 0) :
    (∑ j ∈ Finset.range n, f (θ + (j : ℝ) * α)) ≤ (Work.TMComp.shiftCount α θ δ n : ℝ) := by
  classical
  -- pass to a sum over `Fin n`, so that the index set matches the one in `shiftCount`
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => f (θ + (j : ℝ) * α)) n]
  set s : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => Work.TMContract.fracDist (θ + (j : ℝ) * α) < δ) with hs
  -- the summands outside `s` vanish
  have key : (∑ j : Fin n, f (θ + (j : ℝ) * α)) = ∑ j ∈ s, f (θ + (j : ℝ) * α) := by
    rw [eq_comm]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    have hnot : ¬ (Work.TMContract.fracDist (θ + (j : ℝ) * α) < δ) := by
      intro hcon
      exact hj (by simp [hs, hcon])
    exact h2 _ (not_lt.mp hnot)
  rw [key]
  have hle : ∑ j ∈ s, f (θ + (j : ℝ) * α) ≤ ∑ j ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun j _ => h1 _)
  have hcard : (∑ j ∈ s, (1 : ℝ)) = (s.card : ℝ) := by simp
  have hshift : s.card = Work.TMComp.shiftCount α θ δ n := by rw [hs]; rfl
  calc ∑ j ∈ s, f (θ + (j : ℝ) * α) ≤ ∑ j ∈ s, (1 : ℝ) := hle
    _ = (s.card : ℝ) := hcard
    _ = (Work.TMComp.shiftCount α θ δ n : ℝ) := by rw [hshift]

end Work.TMComp.IDSEqui
