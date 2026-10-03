import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

/-- If all coefficients of `g` except possibly the `j₀`-th vanish, then the skew convolution
formula `(f * g).1 n = ∑ k ∈ Icc (lo f) (n - lo g), f.1 k * (τ^k (g.1 (n - k)))` collapses to the
single term `f.1 (n - j₀) * (τ^{n - j₀} (g.1 j₀))`, i.e. the summand indexed by `k = n - j₀`. -/
theorem mul_apply_eq_single_right {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g : Work.ORHughesFree.SkewLaurentSeries A) (j₀ n : ℤ)
    (hg : ∀ j : ℤ, j ≠ j₀ → g.1 j = 0) :
    (f * g).1 n = f.1 (n - j₀) * ((Multiplicative.ofAdd (n - j₀)) • g.1 j₀) := by
  rw [mul_apply_of_bounds f g (lo f) j₀ (fun m hm => lt_lo hm) (fun m hm => hg m (by omega)) n]
  have hnj : n - (n - j₀) = j₀ := by omega
  have hmain : ∑ k ∈ Finset.Icc (lo f) (n - j₀),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))
      = f.1 (n - j₀) * ((Multiplicative.ofAdd (n - j₀)) • g.1 j₀) := by
    have h := Finset.sum_eq_single (s := Finset.Icc (lo f) (n - j₀))
      (f := fun k => f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))) (n - j₀) ?_ ?_
    · simpa [hnj] using h
    · intro k hk hkne
      rw [hg (n - k) (by omega), smul_zero, mul_zero]
    · intro h
      have hlt : n - j₀ < lo f := by
        by_contra hc
        exact h (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      rw [hnj, lt_lo (f := f) hlt, zero_mul]
  exact hmain

end Work.ORHughesFree.SkewLaurentSeries
