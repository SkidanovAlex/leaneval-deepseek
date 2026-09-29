import Mathlib

/-!
# Summation along anti-diagonals

For a summable family `a : ℕ × ℕ → ℂ`, the anti-diagonal sums
`k ↦ ∑_{m ≤ k} a (m, k - m)` form a summable family whose total sum is `∑' p, a p`.

The proof groups the terms of `a` according to the value of `p.1 + p.2`
(`HasSum.tsum_fiberwise`) and identifies each fiber with an anti-diagonal.
-/

namespace Work.RedProj

theorem hasSum_sum_antidiagonal {a : ℕ × ℕ → ℂ} (ha : Summable a) :
    HasSum (fun k : ℕ => ∑ m ∈ Finset.range (k + 1), a (m, k - m)) (∑' p, a p) := by
  -- Group the terms of `a` according to the value of `p.1 + p.2`.
  have h1 := ha.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 + p.2)
  -- The fiber of `k` under `p ↦ p.1 + p.2` is the `k`-th anti-diagonal.
  have h2 : (fun k : ℕ => ∑' b : ↑((fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {k}), a ↑b)
      = fun k : ℕ => ∑ m ∈ Finset.range (k + 1), a (m, k - m) := by
    funext k
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk a k]
    rw [← Finset.tsum_subtype' (Finset.HasAntidiagonal.antidiagonal (A := ℕ) k) a]
    rw [show ((fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {k} : Set (ℕ × ℕ)) =
        (↑(Finset.HasAntidiagonal.antidiagonal (A := ℕ) k) : Set (ℕ × ℕ)) from by
      ext p; simp]
  rw [h2] at h1
  exact h1

end Work.RedProj
