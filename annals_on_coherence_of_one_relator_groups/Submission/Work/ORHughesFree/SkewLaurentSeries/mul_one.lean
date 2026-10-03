import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Right multiplication by the unit `1` of `A((t;τ))` is the identity.

Using the bound `-1` for `1` (rather than the opaque `lo 1`), the product `f * 1` is, at `n`, the
sum of `f_k * (k • 1_{n-k})` over `k ∈ [lo f, n + 1]`.  Every term with `k ≠ n` vanishes because
`1_{n-k} = 0` there, and the term with `k = n` is `f_n * (n • 1) = f_n`.  Thus the sum is `f_n`
when `lo f ≤ n`, and `0 = f_n` (by definition of `lo`) otherwise. -/
theorem mul_one {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : f * 1 = f := by
  apply Subtype.ext
  funext n
  rw [mul_apply_of_bounds f 1 (lo f) (-1) (fun m hm => lt_lo hm)
    (fun m hm => by rw [one_apply, if_neg (by omega : m ≠ 0)]) n]
  trans ∑ k ∈ Finset.Icc (lo f) (n - (-1)), (if k = n then f.1 n else 0)
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hkn : k = n
    · subst hkn
      simp
    · rw [one_apply, if_neg (by omega : n - k ≠ 0), smul_zero, mul_zero, if_neg hkn]
  · rw [Finset.sum_ite_eq']
    by_cases hle : lo f ≤ n
    · have hmem : n ∈ Finset.Icc (lo f) (n - (-1)) := by
        rw [Finset.mem_Icc]; omega
      rw [if_pos hmem]
    · have hmem : n ∉ Finset.Icc (lo f) (n - (-1)) := by
        rw [Finset.mem_Icc]; omega
      rw [if_neg hmem, lt_lo (not_le.mp hle)]

end Work.ORHughesFree.SkewLaurentSeries
