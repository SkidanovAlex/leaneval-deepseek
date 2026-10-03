import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Left multiplication by the unit `1` of `A((t;τ))` is the identity.

The product `1 * f` is, at `n`, the sum of `1_k * (k • f (n - k))` over
`k ∈ [lo 1, n - lo f]`.  Every term with `k ≠ 0` vanishes because `1_k = 0`, and the term with
`k = 0` is `f n`.  So the sum is `f n` when `0` lies in the summation range, and `0` otherwise --
but if `0` is outside the range then either `n < lo f`, where `f n = 0` by definition of `lo`, or
`0 < lo 1`, in which case `lt_lo` applied at `n = 0` gives `1 = 0` in `A` and hence `f n = 0`. -/
theorem one_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : 1 * f = f := by
  by_cases h1 : lo (1 : SkewLaurentSeries A) ≤ 0
  · apply Subtype.ext; funext n
    rw [mul_apply]
    trans ∑ k ∈ Finset.Icc (lo (1 : SkewLaurentSeries A)) (n - lo f),
        (if k = 0 then f.1 n else 0)
    · refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [Finset.sum_ite_eq']
      by_cases hle : lo f ≤ n
      · have hmem : (0 : ℤ) ∈ Finset.Icc (lo (1 : SkewLaurentSeries A)) (n - lo f) := by
          rw [Finset.mem_Icc]; exact ⟨h1, by omega⟩
        simp [hmem]
      · have hle' : n < lo f := not_le.mp hle
        have hmem : (0 : ℤ) ∉ Finset.Icc (lo (1 : SkewLaurentSeries A)) (n - lo f) := by
          rw [Finset.mem_Icc]; omega
        rw [if_neg hmem, lt_lo hle']
  · have hzero : (1 : A) = 0 := by
      have h := lt_lo (f := (1 : SkewLaurentSeries A)) (n := 0) (not_le.mp h1)
      simpa using h
    apply Subtype.ext; funext n
    rw [mul_apply]
    rw [Finset.sum_eq_zero]
    · have hfn : f.1 n = 0 := by rw [← mul_one (f.1 n), hzero, mul_zero]
      rw [hfn]
    · intro k hk
      by_cases hk0 : k = 0 <;> simp [hzero, hk0]

end Work.ORHughesFree.SkewLaurentSeries
