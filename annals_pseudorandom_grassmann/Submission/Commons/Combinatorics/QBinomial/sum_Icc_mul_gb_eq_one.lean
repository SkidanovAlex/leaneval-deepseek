import Mathlib
import Submission.Commons.Combinatorics.QBinomial.exists_inclusion_exclusion_seq

namespace Commons.Combinatorics.QBinomial

/-- If `a` satisfies the recursive relation
`a k = 1 - ∑_{i=1}^{k-1} a i * [k choose i]_2` for all `k ≥ 1`, then
`∑_{i=1}^{t} a i * [t choose i]_2 = 1` for every `t ≥ 1`. -/
theorem sum_Icc_mul_gb_eq_one (d : ℕ) (a : ℕ → ℤ)
    (ha : ∀ k : ℕ, 1 ≤ k →
      a k = 1 - ∑ i ∈ Finset.Icc 1 (k - 1),
        a i * (Commons.Combinatorics.QBinomial.gb k i : ℤ)) :
    ∀ t : ℕ, 1 ≤ t → t ≤ d →
      ∑ i ∈ Finset.Icc 1 t, a i * (Commons.Combinatorics.QBinomial.gb t i : ℤ) = 1 := by
  intro t ht1 _
  have hsplit : Finset.Icc 1 t = insert t (Finset.Icc 1 (t - 1)) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : t ∉ Finset.Icc 1 (t - 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert hnot, gb_self t, Nat.cast_one, mul_one]
  have h := ha t ht1
  linarith

end Commons.Combinatorics.QBinomial
