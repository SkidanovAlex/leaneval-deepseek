import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

/-- If all coefficients of `f` except possibly the `i₀`-th vanish, then the skew convolution
formula `(f * g).1 n = ∑ k ∈ Icc (lo f) (n - lo g), f.1 k * (τ^k (g.1 (n - k)))` collapses to the
single term `f.1 i₀ * (τ^{i₀} (g.1 (n - i₀)))`. -/
theorem mul_apply_eq_single {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g : Work.ORHughesFree.SkewLaurentSeries A) (i₀ n : ℤ)
    (hf : ∀ j : ℤ, j ≠ i₀ → f.1 j = 0) :
    (f * g).1 n = f.1 i₀ * ((Multiplicative.ofAdd i₀) • g.1 (n - i₀)) := by
  rw [mul_apply]
  -- the summand vanishes away from `k = i₀`, so the sum is its `i₀`-th term
  refine Finset.sum_eq_single i₀ ?_ ?_
  · intro k _ hk
    rw [hf k hk, zero_mul]
  · -- if `i₀` lies outside the summation range, both sides vanish
    intro hi
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    rcases hi with h | h
    · rw [lt_lo h, zero_mul]
    · have hm : n - i₀ < lo g := by omega
      rw [lt_lo hm, smul_zero, mul_zero]

end Work.ORHughesFree.SkewLaurentSeries
