import Mathlib

namespace Work.WilC4aP

/-- A Cauchy-type root bound for the monic polynomial
`X^k + ∑_{i<k} a_i X^i` whose lower coefficients satisfy `‖a i‖ ≤ m`.

If `k * m < σ` and `k * m < σ^k`, every complex root lies strictly inside the disc of
radius `σ`.

The proof: put `r = ‖β‖` and suppose `σ ≤ r`. Evaluating the vanishing of the polynomial at
`β` gives `β^k = -∑_{i<k} a_i β^i`, hence `r^k ≤ m ∑_{i<k} r^i`.

* If `r ≤ 1`, then `∑_{i<k} r^i ≤ k`, so `r^k ≤ k m < σ^k ≤ r^k`, a contradiction.
* If `1 < r`, then `r^i ≤ r^{k-1}` for every `i < k`, so `r^k ≤ k m r^{k-1}`, and dividing
  by `r^{k-1} > 0` gives `r ≤ k m < σ ≤ r`, a contradiction. -/
theorem norm_root_lt_of_coeffs_le {k : ℕ} (hk : 0 < k) (a : Fin k → ℂ) {m σ : ℝ}
    (hm : 0 ≤ m) (hσ : 0 < σ) (ha : ∀ i, ‖a i‖ ≤ m)
    (hmσ : (k : ℝ) * m < σ) (hmσ' : (k : ℝ) * m < σ ^ k) :
    ∀ β : ℂ,
      (Polynomial.X ^ k + ∑ i : Fin k, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).eval β = 0 →
      ‖β‖ < σ := by
  intro β hβ
  by_contra hcon
  have hcon : σ ≤ ‖β‖ := le_of_not_gt hcon
  -- Rewrite the vanishing of the polynomial as a plain identity in `β`.
  have heval : β ^ k + ∑ i : Fin k, a i * β ^ (i : ℕ) = 0 := by
    simpa only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C] using hβ
  -- `‖β‖^k = ‖∑_{i<k} a_i β^i‖`.
  have hrpow : ‖β‖ ^ k = ‖∑ i : Fin k, a i * β ^ (i : ℕ)‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left heval, norm_neg]
  -- Termwise norm bound on the sum.
  have hsum_bound : ‖∑ i : Fin k, a i * β ^ (i : ℕ)‖ ≤ ∑ i : Fin k, m * ‖β‖ ^ (i : ℕ) := by
    calc ‖∑ i : Fin k, a i * β ^ (i : ℕ)‖
        ≤ ∑ i : Fin k, ‖a i * β ^ (i : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin k, m * ‖β‖ ^ (i : ℕ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right (ha i) (by positivity)
  have hmain : ‖β‖ ^ k ≤ m * ∑ i : Fin k, ‖β‖ ^ (i : ℕ) := by
    rw [hrpow]
    calc ‖∑ i : Fin k, a i * β ^ (i : ℕ)‖
        ≤ ∑ i : Fin k, m * ‖β‖ ^ (i : ℕ) := hsum_bound
      _ = m * ∑ i : Fin k, ‖β‖ ^ (i : ℕ) := by rw [Finset.mul_sum]
  rcases le_or_gt ‖β‖ 1 with hle | hlt
  · -- Small root: `r ≤ 1`.
    have hsumk : ∑ i : Fin k, ‖β‖ ^ (i : ℕ) ≤ (k : ℝ) := by
      calc ∑ i : Fin k, ‖β‖ ^ (i : ℕ) ≤ ∑ _i : Fin k, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_one₀ (norm_nonneg β) hle
        _ = (k : ℝ) := by simp
    have hrk_le : ‖β‖ ^ k ≤ (k : ℝ) * m := by
      calc ‖β‖ ^ k ≤ m * ∑ i : Fin k, ‖β‖ ^ (i : ℕ) := hmain
        _ ≤ m * (k : ℝ) := mul_le_mul_of_nonneg_left hsumk hm
        _ = (k : ℝ) * m := by ring
    have hσk : σ ^ k ≤ ‖β‖ ^ k := pow_le_pow_left₀ hσ.le hcon k
    linarith [hmσ']
  · -- Large root: `1 < r`.
    have hsumk : ∑ i : Fin k, ‖β‖ ^ (i : ℕ) ≤ (k : ℝ) * ‖β‖ ^ (k - 1) := by
      calc ∑ i : Fin k, ‖β‖ ^ (i : ℕ) ≤ ∑ _i : Fin k, ‖β‖ ^ (k - 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_right₀ hlt.le (Nat.le_sub_one_of_lt i.isLt)
        _ = (k : ℝ) * ‖β‖ ^ (k - 1) := by simp
    have hrk_le : ‖β‖ ^ k ≤ ((k : ℝ) * m) * ‖β‖ ^ (k - 1) := by
      calc ‖β‖ ^ k ≤ m * ∑ i : Fin k, ‖β‖ ^ (i : ℕ) := hmain
        _ ≤ m * ((k : ℝ) * ‖β‖ ^ (k - 1)) := mul_le_mul_of_nonneg_left hsumk hm
        _ = ((k : ℝ) * m) * ‖β‖ ^ (k - 1) := by ring
    have hpos : 0 < ‖β‖ ^ (k - 1) := pow_pos (lt_trans zero_lt_one hlt) _
    have hpow : ‖β‖ ^ k = ‖β‖ ^ (k - 1) * ‖β‖ := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
      rw [pow_succ]
    have h' : ‖β‖ ^ (k - 1) * ‖β‖ ≤ ‖β‖ ^ (k - 1) * ((k : ℝ) * m) := by
      rw [← hpow]
      calc ‖β‖ ^ k ≤ ((k : ℝ) * m) * ‖β‖ ^ (k - 1) := hrk_le
        _ = ‖β‖ ^ (k - 1) * ((k : ℝ) * m) := by ring
    have hr_le : ‖β‖ ≤ (k : ℝ) * m := (mul_le_mul_iff_of_pos_left hpos).mp h'
    linarith [hmσ]

end Work.WilC4aP
