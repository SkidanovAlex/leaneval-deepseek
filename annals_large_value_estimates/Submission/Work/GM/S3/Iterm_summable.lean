import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

open Finset
open scoped BigOperators

/-- Norm of a triple sum with a uniform bound on the summand:
`‖∑_{t₁∈W}∑_{t₂∈W}∑_{t₃∈W} F t₁ t₂ t₃‖ ≤ |W|³ b` whenever `‖F t₁ t₂ t₃‖ ≤ b` on `W³`.
(Three applications of the triangle inequality, then `∑_{t∈W} 1 = |W|`.) -/
lemma norm_sum_triple_le (W : Finset ℝ) (F : ℝ → ℝ → ℝ → ℂ) (b : ℝ)
    (h : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W, ‖F t₁ t₂ t₃‖ ≤ b) :
    ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, F t₁ t₂ t₃‖ ≤ (W.card : ℝ) ^ 3 * b := by
  calc ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, F t₁ t₂ t₃‖
      ≤ ∑ t₁ ∈ W, ‖∑ t₂ ∈ W, ∑ t₃ ∈ W, F t₁ t₂ t₃‖ := norm_sum_le _ _
    _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ t₃ ∈ W, F t₁ t₂ t₃‖ :=
          Finset.sum_le_sum fun t₁ _ => norm_sum_le _ _
    _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖F t₁ t₂ t₃‖ :=
          Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ _ => norm_sum_le _ _
    _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, b :=
          Finset.sum_le_sum fun t₁ h1 => Finset.sum_le_sum fun t₂ h2 =>
            Finset.sum_le_sum fun t₃ h3 => h t₁ h1 t₂ h2 t₃ h3
    _ = (W.card : ℝ) ^ 3 * b := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring

/-- `Iterm N W ·` is absolutely summable on `ℤ³` as soon as a single nonnegative summable
majorant `β` bounds every `‖ĥ_(t-s)(mN)‖` with `t,s ∈ W`: compare with the product majorant
`β m.1 · β m.2.1 · β m.2.2`, which is summable by `summable_mul_of_summable_norm` applied twice. -/
theorem Iterm_summable (N : ℕ) (W : Finset ℝ) (β : ℤ → ℝ) (hβn : ∀ m : ℤ, 0 ≤ β m)
    (hβS : Summable β)
    (hβ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ,
      ‖Submission.GM.hhat (t - s) ((m : ℝ) * N)‖ ≤ β m) :
    Summable (fun m : ℤ × ℤ × ℤ => ‖Submission.GM.Iterm N W m‖) := by
  -- The pointwise majorant: `‖Iterm N W m‖ ≤ N³ |W|³ β m.1 β m.2.1 β m.2.2`.
  have hbound : ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤
        (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * (β m.1 * β m.2.1 * β m.2.2) := by
    intro m
    rw [Submission.GM.Iterm, norm_mul, norm_pow, Complex.norm_natCast]
    have hterm : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
        ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤
          β m.1 * β m.2.1 * β m.2.2 := by
      intro t₁ ht₁ t₂ ht₂ t₃ ht₃
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul (hβ t₁ t₂ ht₁ ht₂ m.1) (hβ t₂ t₃ ht₂ ht₃ m.2.1) (norm_nonneg _) (hβn _))
        (hβ t₃ t₁ ht₃ ht₁ m.2.2) (norm_nonneg _) (mul_nonneg (hβn _) (hβn _))
    have hsum : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        (Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N))‖ ≤
        (W.card : ℝ) ^ 3 * (β m.1 * β m.2.1 * β m.2.2) :=
      norm_sum_triple_le W
        (fun t₁ t₂ t₃ => Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N))
        (β m.1 * β m.2.1 * β m.2.2) hterm
    calc (N : ℝ) ^ 3 * ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          (Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
              Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
              Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N))‖
        ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (β m.1 * β m.2.1 * β m.2.2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * (β m.1 * β m.2.1 * β m.2.2) := by ring
  -- Summability of the product majorant `β m.1 * β m.2.1 * β m.2.2`.
  have h2 : Summable (fun q : ℤ × ℤ => β q.1 * β q.2) :=
    summable_mul_of_summable_norm hβS.norm hβS.norm
  have h3 : Summable (fun m : ℤ × ℤ × ℤ => β m.1 * (β m.2.1 * β m.2.2)) :=
    summable_mul_of_summable_norm hβS.norm h2.norm
  have hmaj : Summable (fun m : ℤ × ℤ × ℤ => β m.1 * β m.2.1 * β m.2.2) := by
    simpa only [mul_assoc] using h3
  have hc : Summable (fun m : ℤ × ℤ × ℤ =>
      (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * (β m.1 * β m.2.1 * β m.2.2)) :=
    Summable.mul_left _ hmaj
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hbound m) hc

end Work.GM.S3
