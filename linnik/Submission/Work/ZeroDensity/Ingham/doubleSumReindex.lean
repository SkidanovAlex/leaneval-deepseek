import Mathlib

namespace Work.ZeroDensity.Ingham

/-!
# Reindexing a triangular double sum

The elementary identity underlying the passage from the "upper triangle" double
sum `∑_{m ≤ N} ∑_{m < n ≤ N}` to the "lower triangle" double sum
`∑_{n ≤ N} ∑_{m < n}`:  both sides sum the same function over the same set of
pairs `(m,n)` with `1 ≤ m < n ≤ N`, only the order of summation differs.

The proof is purely Finset bookkeeping:  the inner ranges are rewritten as
filters of `Finset.Icc 1 N`, the conditional sums are converted with
`Finset.sum_filter`, the two sums are interchanged with `Finset.sum_comm`, and
the filters are converted back to `Finset.Ico 1 n`.
-/

/-- Both sides of the identity sum `f m n` over the pairs `1 ≤ m < n ≤ N`. -/
theorem doubleSumReindex {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N, f m n)
      = ∑ n ∈ Finset.Ico 1 (N+1), ∑ m ∈ Finset.Ico 1 n, f m n := by
  -- The upper-triangular inner range is the `n ∈ Icc 1 N` with `m < n`.
  have h1 : ∀ m : ℕ, Finset.Icc (m+1) N = (Finset.Icc 1 N).filter (fun n => m < n) := by
    intro m
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  -- The lower-triangular range `Ico 1 n` is the `m ∈ Icc 1 N` with `m < n`.
  have h2 : ∀ n ∈ Finset.Icc 1 N, (Finset.Icc 1 N).filter (fun m => m < n) = Finset.Ico 1 n := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  -- `Ico 1 (N+1)` is the same range as `Icc 1 N`.
  have h3 : Finset.Ico 1 (N+1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  calc ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N, f m n
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n), f m n := by
        apply Finset.sum_congr rfl; intro m _
        rw [h1 m]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if m < n then f m n else 0) := by
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, (if m < n then f m n else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ico 1 n, f m n := by
        apply Finset.sum_congr rfl; intro n hn
        rw [← Finset.sum_filter, h2 n hn]
    _ = ∑ n ∈ Finset.Ico 1 (N+1), ∑ m ∈ Finset.Ico 1 n, f m n := by
        rw [h3]

end Work.ZeroDensity.Ingham
