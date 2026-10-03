import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6Hecke.R

open Finset

/-- Fibre double-counting for an arbitrary finite index set: summing, over `n ∈ {1,…,M}`, the
`F`-sum over the fibre `f = n`, is the same as the `F`-sum over the elements whose value lies in
`{1,…,M}`. -/
lemma sum_fiber_Icc {α : Type*} (s : Finset α) (f : α → ℕ) (F : α → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, ∑ z ∈ s.filter (fun z => f z = n), F z)
      = ∑ z ∈ s.filter (fun z => 1 ≤ f z ∧ f z ≤ M), F z := by
  rw [show (∑ n ∈ Finset.Icc 1 M, ∑ z ∈ s.filter (fun z => f z = n), F z)
        = ∑ n ∈ Finset.Icc 1 M, ∑ z ∈ s, (if f z = n then F z else 0) from by
      apply Finset.sum_congr rfl; intro n _; rw [Finset.sum_filter]]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_ite_eq]
  simp

/-- Double-counting (fibre) identity: summing over `n ∈ {1,…,M}` the sum over Gaussian integers
in `gBox M` of norm exactly `n` is the same as summing over all `z ∈ gBox M` with
`1 ≤ |z|² ≤ M`.  (`Finset.sum_fiberwise_of_maps_to'` with `gnorm`, or `Finset.sum_comm` plus
`Finset.sum_filter`; the two index sets are `Icc 1 M` and `gBox M` filtered by
`1 ≤ gnorm z ∧ gnorm z ≤ M`.)  Note `F` is arbitrary (no sign or support hypothesis needed):
each `z` with `1 ≤ |z|² ≤ M` lies in exactly one fibre, and every fibre already sits inside
`gBox M`.  For `M = 0` both sides are `0`. -/
theorem LamSumFibre (M : ℕ) (F : GaussianInt → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,
        ∑ z ∈ (Work.FIPlan.gBox (M : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n), F z)
      = ∑ z ∈ (Work.FIPlan.gBox (M : ℤ)).filter
          (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ M), F z := by
  exact sum_fiber_Icc (Work.FIPlan.gBox (M : ℤ)) Work.FIPlan.gnorm F M

end Work.FIArea6Hecke.R
