import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Main

/-- Pure real-arithmetic core of `theta_shift_bound`.

With `Q = q n`, `Q' = q (n+1)`, `d = Δ n`, the hypotheses are exactly
`1 ≤ Q`, `0 < Q'`, `0 ≤ d`, `d < 1/Q'`, `(4Q)^9 ≤ Q'` and `B0 ≤ Q'/Q`, and the
conclusion is the required inequality.  The only numerically relevant ingredient is
`17 Q² + 8 Q ≤ 2 Q'`, which follows from `Q' ≥ (4Q)^9 ≥ 262144 Q²` for `Q ≥ 1`. -/
lemma theta_shift_arith {Q Q' B0 d : ℝ} (hQ1 : 1 ≤ Q) (hQ' : 0 < Q')
    (hd0 : 0 ≤ d) (hd : d < 1 / Q') (h4 : (4 * Q) ^ 9 ≤ Q') (hB : B0 ≤ Q' / Q) :
    ((B0 + 8 * Q + 4) / Q + 1 / 2) * d ≤ 2 / Q ^ 2 := by
  have hQ : 0 < Q := lt_of_lt_of_le one_pos hQ1
  -- Key numeric estimate.
  have hQQ : 17 * Q ^ 2 + 8 * Q ≤ 2 * Q' := by
    have hpow : (4 * Q) ^ 9 = 262144 * Q ^ 9 := by ring
    have hQ9 : Q ^ 2 ≤ Q ^ 9 := pow_le_pow_right₀ hQ1 (by norm_num : (2:ℕ) ≤ 9)
    have hbig : 262144 * Q ^ 2 ≤ Q' := by
      rw [hpow] at h4
      exact le_trans (mul_le_mul_of_nonneg_left hQ9 (by norm_num)) h4
    nlinarith [hbig, sq_nonneg Q, hQ1]
  set C : ℝ := 2 * B0 + 17 * Q + 8 with hCdef
  set C' : ℝ := 2 * Q' / Q + 17 * Q + 8 with hC'def
  have hC'pos : 0 < C' := by rw [hC'def]; positivity
  have hCC' : C ≤ C' := by
    rw [hCdef, hC'def]
    have h2 : (2:ℝ) * B0 ≤ 2 * Q' / Q := by
      have := mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2)
      simpa only [mul_div_assoc] using this
    linarith
  have hstep1 : C * d ≤ C' * d := mul_le_mul_of_nonneg_right hCC' hd0
  have hstep2 : C' * d < C' * (1 / Q') := mul_lt_mul_of_pos_left hd hC'pos
  have h1 : C * d * Q ≤ C' * d * Q := mul_le_mul_of_nonneg_right hstep1 (le_of_lt hQ)
  have h2 : C' * d * Q ≤ C' * (1 / Q') * Q :=
    mul_le_mul_of_nonneg_right (le_of_lt hstep2) (le_of_lt hQ)
  have h3 : C' * (1 / Q') * Q ≤ 4 := by
    have hEq : C' * (1 / Q') * Q = (2 * Q' + 17 * Q ^ 2 + 8 * Q) / Q' := by
      rw [hC'def]; field_simp
    rw [hEq, div_le_iff₀ hQ']
    nlinarith [hQQ]
  have hCdQ : C * d * Q ≤ 4 := le_trans h1 (le_trans h2 h3)
  have key : ((B0 + 8 * Q + 4) / Q + 1 / 2) * d = C * d / (2 * Q) := by
    rw [hCdef]; field_simp; ring
  rw [key, div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * Q) (by nlinarith [hQ] : (0:ℝ) < Q ^ 2)]
  have hconv : C * d * Q ^ 2 = (C * d * Q) * Q := by ring
  rw [hconv]
  nlinarith [mul_le_mul_of_nonneg_right hCdQ (le_of_lt hQ)]

theorem theta_shift_bound {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {B0 : ℝ}
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hcase1 : (4 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) ∧
        B0 ≤ (q (n + 1) : ℝ) / (q n : ℝ)) :
    ((B0 + 8 * (q n : ℝ) + 4) / (q n : ℝ) + 1 / 2) * Δ n ≤ 2 / (q n : ℝ) ^ 2 := by
  obtain ⟨h4, hB⟩ := hcase1
  have hqn : 1 ≤ q n := Nat.succ_le_of_lt (hqpos n)
  have hQ1 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqn
  have hQ' : (0:ℝ) < (q (n + 1) : ℝ) := by exact_mod_cast hqpos (n + 1)
  have hd0 : 0 ≤ Δ n := by
    rw [hΔeq n]; exact abs_nonneg _
  exact theta_shift_arith hQ1 hQ' hd0 (hΔup n) h4 hB

end Work.TMC16Core.Main
