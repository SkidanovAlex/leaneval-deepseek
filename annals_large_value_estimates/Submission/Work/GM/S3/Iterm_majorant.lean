import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- Pointwise majorant for `Iterm` (GM Lemma 4.5).  `Iterm N W m` is `N³` times the triple sum
over `t₁,t₂,t₃ ∈ W` of `ĥ(t₁-t₂,m₁N)·ĥ(t₂-t₃,m₂N)·ĥ(t₃-t₁,m₃N)`.  If for every `t,s ∈ W` the
three factors are bounded by the reals `b₁,b₂,b₃`, then the triangle inequality and
`∑_{t ∈ W} 1 = |W|` give `‖Iterm N W m‖ ≤ N³·|W|³·b₁·b₂·b₃`. -/
theorem Iterm_majorant (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (b₁ b₂ b₃ : ℝ)
    (h₁ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ‖Submission.GM.hhat (t - s) ((m.1 : ℝ) * N)‖ ≤ b₁)
    (h₂ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ‖Submission.GM.hhat (t - s) ((m.2.1 : ℝ) * N)‖ ≤ b₂)
    (h₃ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ‖Submission.GM.hhat (t - s) ((m.2.2 : ℝ) * N)‖ ≤ b₃) :
    ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * (b₁ * b₂ * b₃) := by
  classical
  rw [Submission.GM.Iterm]
  by_cases hW : W = ∅
  · subst hW
    simp
  · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW
    obtain ⟨t0, ht0⟩ := hne
    have hb1 : 0 ≤ b₁ := le_trans (norm_nonneg _) (h₁ t0 t0 ht0 ht0)
    have hb2 : 0 ≤ b₂ := le_trans (norm_nonneg _) (h₂ t0 t0 ht0 ht0)
    have hb3 : 0 ≤ b₃ := le_trans (norm_nonneg _) (h₃ t0 t0 ht0 ht0)
    have hnorm : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
        ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
          Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
          Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤ b₁ * b₂ * b₃ := by
      intro t₁ ht₁ t₂ ht₂ t₃ ht₃
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul (h₁ t₁ t₂ ht₁ ht₂) (h₂ t₂ t₃ ht₂ ht₃) (norm_nonneg _) hb1)
        (h₃ t₃ t₁ ht₃ ht₁) (norm_nonneg _) (mul_nonneg hb1 hb2)
    have hsum : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
          Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
          Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
        ≤ (W.card : ℝ) ^ 3 * (b₁ * b₂ * b₃) := by
      calc
        ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
            ≤ ∑ t₁ ∈ W, ‖∑ t₂ ∈ W, ∑ t₃ ∈ W,
                Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
                  Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
                  Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ :=
              norm_sum_le _ _
        _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ t₃ ∈ W,
                Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
                  Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
                  Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ := by
              apply Finset.sum_le_sum
              intro t₁ ht₁
              exact norm_sum_le _ _
        _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
              ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
                Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
                Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ := by
              apply Finset.sum_le_sum
              intro t₁ ht₁
              apply Finset.sum_le_sum
              intro t₂ ht₂
              exact norm_sum_le _ _
        _ ≤ ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, (b₁ * b₂ * b₃) := by
              apply Finset.sum_le_sum
              intro t₁ ht₁
              apply Finset.sum_le_sum
              intro t₂ ht₂
              apply Finset.sum_le_sum
              intro t₃ ht₃
              exact hnorm t₁ ht₁ t₂ ht₂ t₃ ht₃
        _ = (W.card : ℝ) ^ 3 * (b₁ * b₂ * b₃) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              ring
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      (N : ℝ) ^ 3 * ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (b₁ * b₂ * b₃)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * (b₁ * b₂ * b₃) := by ring

end Work.GM.S3
