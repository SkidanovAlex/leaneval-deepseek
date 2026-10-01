import Mathlib

namespace Work.ZeroDensity.Ingham

/-!
# Swapping the order of summation over a triangular region of indices

The double sum `∑_{2 ≤ k ≤ M} ∑_{1 ≤ n ≤ k} f n k` ranges over the pairs
`(n,k)` with `2 ≤ k ≤ M` and `1 ≤ n ≤ k`, i.e. over the *lower* triangle of the
box `[1,M] × [2,M]`.  Collecting the pairs by their first coordinate instead
gives the *upper* description `1 ≤ n ≤ M`, `max 2 n ≤ k ≤ M`, which is the
identity

`∑_{k=2}^{M} ∑_{n=1}^{k} f n k = ∑_{n=1}^{M} ∑_{k=max 2 n}^{M} f n k`.

The proof has three elementary steps:

* for `k ≤ M` the fibre `Icc 1 k` is `(Icc 1 M).filter (· ≤ k)`, so the inner
  sum can be written with the fixed range `Icc 1 M` and an indicator;
* `Finset.sum_comm` interchanges the two (now independent) ranges;
* for `n ≥ 1` the indicator sum over `k ∈ Icc 2 M` is the sum over
  `Icc (max 2 n) M`, via `Icc_filter_le_of_le`.
-/

/-- Restricting `Finset.Icc a b` to the `n` with `c ≤ n` gives
`Finset.Icc (max a c) b`. -/
lemma Icc_filter_le_of_le (a b c : ℕ) :
    (Finset.Icc a b).filter (fun n => c ≤ n) = Finset.Icc (max a c) b := by
  ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem sum_Icc_Icc_swap {α : Type*} [AddCommMonoid α] (M : ℕ) (f : ℕ → ℕ → α) :
    (∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc 1 k, f n k)
      = ∑ n ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc (max 2 n) M, f n k := by
  calc (∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc 1 k, f n k)
      = ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc 1 M, (if n ≤ k then f n k else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
        have hkey : Finset.Icc 1 k = (Finset.Icc 1 M).filter (fun n => n ≤ k) := by
          ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hkey, Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 2 M, (if n ≤ k then f n k else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc (max 2 n) M, f n k := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Finset.sum_filter (s := Finset.Icc 2 M) (p := fun k => n ≤ k)
              (f := fun k => f n k), Icc_filter_le_of_le]

end Work.ZeroDensity.Ingham
