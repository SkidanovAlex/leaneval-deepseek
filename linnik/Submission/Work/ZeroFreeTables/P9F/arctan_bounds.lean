import Mathlib

/-!
# Numerical bounds for `Real.arctan 15`, `Real.arctan 24`, `Real.arctan 25`

The certificate infrastructure of `Work.ZeroFreeTables.P9F` uses `θ = arctan m` with an
integer `m` so that the trigonometric values `tan θ = m`, `sin 2θ`, `cos 2θ`, ... stay
*rational*.  To make such a certificate rigorous one has to know `arctan m` to the precision
printed in the certificate; this file provides those bounds for `m = 15, 24, 25`.

## Method

For `0 ≤ x < 1` the Taylor series of `arctan` at `x` is the alternating series
`arctan x = ∑ (-1)^i x^(2i+1)/(2i+1)` (`Real.hasSum_arctan`).  Its terms are antitone, so the
standard alternating-series error estimate `alternating_series_error_bound` gives

`|arctan x - ∑_{i<n} (-1)^i x^(2i+1)/(2i+1)| ≤ x^(2n+1)/(2n+1)`.

Combining this at `x = 1/m` with the 20-digit bounds on `π` (`Real.pi_gt_d20`,
`Real.pi_lt_d20`) and the reflection formula `arctan m = π/2 - arctan (1/m)`
(`Real.arctan_inv_of_pos`) yields the required rational bounds; all remaining arithmetic is
`norm_num`.
-/

namespace Work.ZeroFreeTables.P9F

/-- The Taylor terms `x^(2i+1)/(2i+1)` of the arctangent series form an antitone sequence
for `0 ≤ x ≤ 1`. -/
lemma arctan_series_term_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) := by
  refine antitone_nat_of_succ_le fun i => ?_
  have hc : (0 : ℝ) ≤ x ^ (2 * i + 1) := pow_nonneg hx0 _
  have hac : x ^ (2 * (i + 1) + 1) ≤ x ^ (2 * i + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have h0d : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
  have hdb : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * (i + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * i + 1 ≤ 2 * (i + 1) + 1 by omega)
  exact div_le_div₀ hc hac h0d hdb

/-- The Taylor terms `x^(2i+1)/(2i+1)` of the arctangent series are summable for
`0 ≤ x < 1`. -/
lemma arctan_series_term_summable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0 2)]
    nlinarith
  refine Summable.of_nonneg_of_le
    (f := fun i : ℕ => x * (x ^ 2) ^ i)
    (g := fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ?_ ?_ ?_
  · intro i
    exact div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
  · intro i
    have h1 : x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) ≤ x ^ (2 * i + 1) := by
      have h : x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) ≤ x ^ (2 * i + 1) / 1 :=
        div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by norm_num)
          (by exact_mod_cast (show 1 ≤ 2 * i + 1 by omega))
      simpa using h
    have h2 : x ^ (2 * i + 1) = x * (x ^ 2) ^ i := by
      rw [← pow_mul, pow_succ']
    calc x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) ≤ x ^ (2 * i + 1) := h1
      _ = x * (x ^ 2) ^ i := h2
  · exact (summable_geometric_of_norm_lt_one hx2).mul_left x

/-- **Alternating-series error estimate for the arctangent Taylor series.**
For `0 ≤ x < 1` and any `n`,
`|arctan x - ∑_{i<n} (-1)^i x^(2i+1)/(2i+1)| ≤ x^(2n+1)/(2n+1)`. -/
lemma arctan_series_error_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    |Real.arctan x - ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))|
      ≤ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hx1' : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hsum := Real.hasSum_arctan (x := x) hx1'
  have hsum' : HasSum (fun n : ℕ => (-1) ^ n * (x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
      (Real.arctan x) := by
    simpa only [mul_div_assoc] using hsum
  have hb := alternating_series_error_bound
      (fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))
      (arctan_series_term_antitone hx0 hx1.le) (arctan_series_term_summable hx0 hx1) n
  rw [hsum'.tsum_eq] at hb
  exact hb

/-- Rational bounds for `Real.arctan x` for `x > 1`, derived from the Taylor series of
`arctan (x⁻¹)` (truncated after `n` terms) and the 20-digit bounds on `π`.

The hypotheses `hA`, `hB` are the two pure-rational inequalities that remain after
inserting the series error `(x⁻¹)^(2n+1)/(2n+1)` and the `π` bounds; they are checked by
`norm_num` at each concrete call site. -/
lemma arctan_of_inv_bounds (x : ℝ) (hx : 1 < x) (n : ℕ) (A B : ℝ)
    (hA : A ≤ (3.14159265358979323846 : ℝ) / 2
        - (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x⁻¹ ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
        - x⁻¹ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
    (hB : (3.14159265358979323847 : ℝ) / 2
        - (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x⁻¹ ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
        + x⁻¹ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤ B) :
    A ≤ Real.arctan x ∧ Real.arctan x ≤ B := by
  have hxpos : 0 < x := lt_trans one_pos hx
  have hxi0 : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr hxpos)
  have hxi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hb := arctan_series_error_bound (x⁻¹) hxi0 hxi1 n
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hinv : Real.arctan x = Real.pi / 2 - Real.arctan x⁻¹ := by
    have := Real.arctan_inv_of_pos hxpos
    linarith
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have phl : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  constructor
  · rw [hinv]; linarith
  · rw [hinv]; linarith

/-- Numerical bounds for `Real.arctan 15`, `Real.arctan 24` and `Real.arctan 25` to
`10^{-12}`. -/
theorem arctan_bounds :
    (1504228163019/10^12 : ℝ) ≤ Real.arctan 15 ∧
    Real.arctan 15 ≤ 1504228163020/10^12 ∧
    (1529153747696/10^12 : ℝ) ≤ Real.arctan 24 ∧
    Real.arctan 24 ≤ 1529153747697/10^12 ∧
    (1530817639671/10^12 : ℝ) ≤ Real.arctan 25 ∧
    Real.arctan 25 ≤ 1530817639672/10^12 := by
  obtain ⟨h15lo, h15hi⟩ := arctan_of_inv_bounds 15 (by norm_num) 6
    (1504228163019/10^12) (1504228163020/10^12) (by norm_num) (by norm_num)
  obtain ⟨h24lo, h24hi⟩ := arctan_of_inv_bounds 24 (by norm_num) 6
    (1529153747696/10^12) (1529153747697/10^12) (by norm_num) (by norm_num)
  obtain ⟨h25lo, h25hi⟩ := arctan_of_inv_bounds 25 (by norm_num) 6
    (1530817639671/10^12) (1530817639672/10^12) (by norm_num) (by norm_num)
  exact ⟨h15lo, h15hi, h24lo, h24hi, h25lo, h25hi⟩

end Work.ZeroFreeTables.P9F
