import Mathlib

/-!
# Comparison of the `ℓ^r`- and `ℓ²`-"norms" of a sequence, for `r ≥ 2`

For a sequence `c : ℕ → ℂ` and a real exponent `r ≥ 2`,

  `(∑'_n ‖c n‖ₑ^r)^{1/r} ≤ (∑'_n ‖c n‖ₑ^2)^{1/2}`,

the discrete-measure case of the monotonicity `‖a‖_{ℓ^q} ≤ ‖a‖_{ℓ^p}` (`q ≥ p`), written with
`ℝ≥0∞`-valued sums so that no summability hypothesis is needed.

The proof is the standard "`ℓ^p ⊆ ℓ^1`" argument, in `ℝ≥0∞`:

* `tsum_rpow_le_rpow_tsum`: for `p ≥ 1` and `b : ℕ → ℝ≥0∞`,
  `∑'_n b n^p ≤ (∑'_n b n)^p` (substitute `b n^p = b n^{p-1} · b n`, bound `b n ≤ ∑'_m b m`,
  and sum the geometric factor out).
* Apply it to `b n = ‖c n‖ₑ^2` and `p = r/2 ≥ 1`, using `(‖c n‖ₑ^2)^{r/2} = ‖c n‖ₑ^r`
  (`ENNReal.rpow_mul`), and conclude by raising both sides to the power `r`
  (`ENNReal.rpow_le_rpow_iff`, `ENNReal.rpow_inv_rpow`, `ENNReal.rpow_mul`).
-/

namespace Work.KMTAreas.A7

open scoped ENNReal BigOperators

/-- `ℓ^p ⊆ ℓ^1` in `ℝ≥0∞`-form: for `p ≥ 1`, the `p`-th-power sum of a `ℝ≥0∞`-sequence is at most
the `p`-th power of its sum.  (For counting measure, `‖b‖_p ≤ ‖b‖_1`.) -/
lemma tsum_rpow_le_rpow_tsum (b : ℕ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑' n : ℕ, b n ^ p ≤ (∑' n : ℕ, b n) ^ p := by
  have hp1 : 0 ≤ p - 1 := by linarith
  -- each summand is `b n^{p-1} · b n`, bounded by `(∑ b)^{p-1} · b n`
  have hterm : ∀ n : ℕ, b n ^ p ≤ (∑' m : ℕ, b m) ^ (p - 1) * b n := by
    intro n
    have hle : b n ≤ ∑' m : ℕ, b m := ENNReal.le_tsum n
    calc b n ^ p = b n ^ ((p - 1) + 1) := by congr 1; ring
      _ = b n ^ (p - 1) * b n ^ (1 : ℝ) := ENNReal.rpow_add_of_nonneg _ _ hp1 (by norm_num)
      _ = b n ^ (p - 1) * b n := by rw [ENNReal.rpow_one]
      _ ≤ (∑' m : ℕ, b m) ^ (p - 1) * b n := by gcongr
  calc ∑' n : ℕ, b n ^ p
      ≤ ∑' n : ℕ, (∑' m : ℕ, b m) ^ (p - 1) * b n := ENNReal.tsum_le_tsum hterm
    _ = (∑' m : ℕ, b m) ^ (p - 1) * ∑' n : ℕ, b n := ENNReal.tsum_mul_left
    _ = (∑' m : ℕ, b m) ^ (p - 1) * (∑' m : ℕ, b m) := rfl
    _ = (∑' m : ℕ, b m) ^ ((p - 1) + 1) := by
          rw [ENNReal.rpow_add_of_nonneg (p - 1) 1 hp1 (by norm_num), ENNReal.rpow_one]
    _ = (∑' m : ℕ, b m) ^ p := by congr 1; ring

/-- For `r ≥ 2`, the `ℓ^r`-"norm" of a complex sequence is dominated by its `ℓ²`-"norm":
`(∑'_n ‖c n‖ₑ^r)^{1/r} ≤ (∑'_n ‖c n‖ₑ^2)^{1/2}`. -/
theorem rpow_tsum_le_sq_tsum {r : ℝ} (hr : 2 ≤ r) (c : ℕ → ℂ) :
    (∑' n : ℕ, ‖c n‖ₑ ^ r) ^ (1 / r) ≤ (∑' n : ℕ, ‖c n‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r / 2 := by linarith
  -- reduce to the inequality `∑ ‖c n‖ₑ^r ≤ (∑ ‖c n‖ₑ^2)^{r/2}`
  have hkey : (∑' n : ℕ, ‖c n‖ₑ ^ r) ≤ (∑' n : ℕ, ‖c n‖ₑ ^ (2 : ℝ)) ^ (r / 2) := by
    calc ∑' n : ℕ, ‖c n‖ₑ ^ r
        = ∑' n : ℕ, (‖c n‖ₑ ^ (2 : ℝ)) ^ (r / 2) := by
            apply tsum_congr; intro n
            rw [← ENNReal.rpow_mul]; congr 1; ring
      _ ≤ (∑' n : ℕ, ‖c n‖ₑ ^ (2 : ℝ)) ^ (r / 2) := tsum_rpow_le_rpow_tsum _ hr1
  -- raise both sides to the power `r`
  have h1 : ((∑' n : ℕ, ‖c n‖ₑ ^ r) ^ (1 / r)) ^ r = ∑' n : ℕ, ‖c n‖ₑ ^ r := by
    rw [one_div]; exact ENNReal.rpow_inv_rpow hr0.ne' _
  have h2 : ((∑' n : ℕ, ‖c n‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ r
      = (∑' n : ℕ, ‖c n‖ₑ ^ (2 : ℝ)) ^ (r / 2) := by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  exact (ENNReal.rpow_le_rpow_iff hr0).mp (by rw [h1, h2]; exact hkey)

end Work.KMTAreas.A7
