/-
# ZeroFreeTables/P3/SummableVonMangoldtLogPow

Absolute convergence of the logarithmic-power weighted von Mangoldt series

`∑_n Λ(n) (log n)^A / n^σ`     (`σ > 1`, `A : ℕ`),

the analytic input behind every absolutely convergent ("Re s > 1") manipulation of the
smoothed von Mangoldt sums `Σ(s,χ)` of HB §8 (see `SigmaP3`).

The argument is elementary but has to be done from scratch: `vonMangoldt n ≤ log n`, so the
`n`-th summand is dominated by `(log n)^{A+1} / n^σ`; the crude pointwise bound
`log x ≤ x^ε / ε` (`ε > 0`) turns `(log x)^k` into a fixed power `x^{ε k}` chosen so that the
resulting series is a convergent `p`-series with exponent `(σ+1)/2 > 1`.
-/
import Mathlib

namespace Work.ZeroFreeTables.P3

open ArithmeticFunction

/-- **Pointwise logarithm bound.** For `σ > 1` and `k ≥ 1` there is a constant `C ≥ 0` with
`log x ^ k ≤ C · x^((σ-1)/2)` for all `x ≥ 1`.

This is the quantitative form of `log x = o(x^ε)`: apply `Real.log_le_rpow_div` with
`ε = (σ-1)/(2k)` and raise to the `k`-th power; the `x`-power `x^{εk} = x^{(σ-1)/2}`
is linear in the exponent, which is exactly what makes the resulting `p`-series converge. -/
lemma log_pow_le_const_mul_rpow {σ : ℝ} (hσ : 1 < σ) {k : ℕ} (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ k ≤ C * x ^ ((σ - 1) / 2) := by
  refine ⟨((((σ - 1) / 2) / (k : ℝ)) ^ k)⁻¹, ?_, ?_⟩
  · exact inv_nonneg.mpr
      (pow_nonneg (le_of_lt (div_pos (by linarith) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)))) k)
  · intro x hx
    set ε : ℝ := ((σ - 1) / 2) / (k : ℝ) with hεdef
    have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hε : 0 < ε := div_pos (by linarith) hkpos
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : (Real.log x) ^ k ≤ (x ^ ε / ε) ^ k :=
      pow_le_pow_left₀ hlog_nonneg (Real.log_le_rpow_div hx0 hε) k
    have h2 : (x ^ ε / ε) ^ k = x ^ (ε * (k : ℝ)) / ε ^ k := by
      rw [div_pow, ← Real.rpow_natCast (x ^ ε) k, ← Real.rpow_mul hx0 ε (k : ℝ)]
    have h3 : ε * (k : ℝ) = (σ - 1) / 2 := by
      rw [hεdef]; field_simp
    rw [h2, h3] at h1
    calc (Real.log x) ^ k ≤ x ^ ((σ - 1) / 2) / ε ^ k := h1
      _ = (ε ^ k)⁻¹ * x ^ ((σ - 1) / 2) := by rw [div_eq_mul_inv, mul_comm]

/-- **The logarithmic `p`-series.** For `σ > 1` and `k ≥ 1` the series
`∑_n (log n)^k / n^σ` converges absolutely. -/
lemma summable_log_pow_div_nat_rpow {σ : ℝ} (hσ : 1 < σ) (k : ℕ) (hk : k ≠ 0) :
    Summable (fun n : ℕ => (Real.log n) ^ k / (n : ℝ) ^ σ) := by
  obtain ⟨C, _hCnn, hCbound⟩ := log_pow_le_const_mul_rpow hσ hk
  have hσpos : (0 : ℝ) < σ := lt_trans zero_lt_one hσ
  have hsum_g : Summable (fun n : ℕ => C * (n : ℝ) ^ (-(σ + 1) / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(σ + 1) / 2 < -1)).mul_left C
  refine Summable.of_norm_bounded hsum_g ?_
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (ne_of_gt hσpos)
    have h1 : (0 : ℝ) ^ (-(σ + 1) / 2) = 0 := Real.zero_rpow (by linarith)
    push_cast
    rw [Real.log_zero, zero_pow hk, h0, zero_div, norm_zero, h1, mul_zero]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hnσpos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hlog_nonneg k) (le_of_lt hnσpos))]
    refine le_trans (div_le_div_of_nonneg_right (hCbound (n : ℝ) hn1) (le_of_lt hnσpos))
      (le_of_eq ?_)
    rw [mul_div_assoc, ← Real.rpow_sub hnpos, show (σ - 1) / 2 - σ = -(σ + 1) / 2 by ring]

/-- **Absolute convergence of the von Mangoldt series with logarithmic weight.**
For `σ > 1` and `A : ℕ` the series `∑_n Λ(n) (log n)^A / n^σ` converges absolutely. -/
theorem SummableVonMangoldtLogPow {σ : ℝ} (hσ : 1 < σ) (A : ℕ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ A / (n : ℝ) ^ σ) := by
  have hsum := summable_log_pow_div_nat_rpow hσ (A + 1) (Nat.succ_ne_zero A)
  refine Summable.of_norm_bounded hsum ?_
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hσ))
    simp [h0, Real.log_zero]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hnσpos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (pow_nonneg hlog_nonneg A)) (le_of_lt hnσpos))]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hnσpos)
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (pow_nonneg hlog_nonneg A)

end Work.ZeroFreeTables.P3
