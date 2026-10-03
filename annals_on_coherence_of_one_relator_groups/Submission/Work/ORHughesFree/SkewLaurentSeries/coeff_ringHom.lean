import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

/-- The coefficient embedding `A → A((t;τ))` is a ring homomorphism.

Addition and the unit are immediate from the definition of `coeff` (`(coeff c).1 n = c` when
`n = 0` and `0` otherwise).  For multiplication, `coeff a` and `coeff b` both vanish below `-1`, so
by `mul_apply_of_bounds` the `n`-th coefficient of `coeff a * coeff b` is the sum of
`a_k * (k • b_{n-k})` over `k ∈ [-1, n+1]`.  Both `a_k` and `b_{n-k}` can be nonzero only when
`k = 0` and `k = n`, so the only surviving term is `a * b`, present exactly when `n = 0`. -/
theorem coeff_ringHom {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (a b : A) : coeff (a * b) = coeff a * coeff b ∧ coeff (a + b) = coeff a + coeff b ∧
      coeff (1 : A) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    funext n
    rw [mul_apply_of_bounds (coeff a) (coeff b) (-1) (-1)
      (fun m hm => by rw [coeff_apply, if_neg (by omega : m ≠ 0)])
      (fun m hm => by rw [coeff_apply, if_neg (by omega : m ≠ 0)]) n]
    rw [coeff_apply]
    have hterm : ∀ k : ℤ, (coeff a).1 k * (Multiplicative.ofAdd k • (coeff b).1 (n - k))
        = if k = 0 then (if n = 0 then a * b else 0) else 0 := by
      intro k
      by_cases hk : k = 0
      · subst hk
        by_cases hn : n = 0
        · subst hn; simp [coeff_apply]
        · simp [coeff_apply, hn]
      · simp only [coeff_apply, if_neg hk, zero_mul]
    rw [show (∑ k ∈ Finset.Icc (-1) (n - (-1)),
            (coeff a).1 k * (Multiplicative.ofAdd k • (coeff b).1 (n - k)))
          = ∑ k ∈ Finset.Icc (-1) (n - (-1)),
            (if k = 0 then (if n = 0 then a * b else 0) else 0) from
        Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_ite_eq']
    by_cases hmem : (0 : ℤ) ∈ Finset.Icc (-1) (n - (-1))
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      have hn : n ≠ 0 := by
        intro h; subst h
        exact hmem (by simp [Finset.mem_Icc])
      rw [if_neg hn]
  · apply Subtype.ext
    funext n
    rw [add_apply]
    by_cases hn : n = 0 <;> simp [coeff_apply, hn]
  · apply Subtype.ext
    funext n
    simp [coeff_apply, one_apply]

end Work.ORHughesFree.SkewLaurentSeries
