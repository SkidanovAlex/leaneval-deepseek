import Mathlib

namespace Work.Fx

/-!
# The numerical bound `exp (z/D) + 4/D ≤ 2^τ`

This is the arithmetic core of the truncation step of the positive exponential field
(paper Lemma 2.14): with `D` a large scale (`D ≥ 2000`) and an integer exponent
`τ ≥ 0`, an `exp` value controlled by `z ≤ τ·log 2·D - 4` is bounded by `2^τ`, with
the usual additive slack `4/D`.  For `τ = 0` the main hypothesis alone is *not*
enough (at `z = -4`, `D = 2000` the sum is `1.000002…`), so the extra hypothesis
`τ = 0 → z ≤ -2000` is needed and is used only there.
-/

/-- For `0 ≤ u ≤ 1` we have `exp (-u) ≤ 1 - u/2`. -/
theorem exp_neg_le_one_sub_half_le_one_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp (-u) ≤ 1 - u / 2 := by
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have hexp : (1 : ℝ) + u ≤ Real.exp u := by
    have := Real.add_one_le_exp u; linarith
  have h1' : (Real.exp u)⁻¹ ≤ ((1 : ℝ) + u)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos u) hpos).mpr hexp
  rw [Real.exp_neg]
  refine le_trans h1' ?_
  rw [← one_div, div_le_iff₀ hpos]
  nlinarith

/-- `exp (τ · log 2) = 2^τ` for a nonnegative integer exponent. -/
theorem exp_intCast_mul_log_two (τ : ℤ) (hτ : 0 ≤ τ) :
    Real.exp ((τ : ℝ) * Real.log 2) = (2 : ℝ) ^ τ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, τ = (n : ℤ) := ⟨τ.toNat, (Int.toNat_of_nonneg hτ).symm⟩
  subst hn
  push_cast
  rw [zpow_natCast, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem ExpPosExpBound (z D : ℝ) (τ : ℤ)
    (hD : 2000 ≤ D) (hτ : 0 ≤ τ)
    (hmain : z ≤ (τ : ℝ) * Real.log 2 * D - 4)
    (hzero : τ = 0 → z ≤ -2000) :
    Real.exp (z / D) + 4 / D ≤ (2 : ℝ) ^ τ := by
  have hDpos : (0 : ℝ) < D := by linarith
  rcases eq_or_lt_of_le hτ with h0 | hpos
  · -- `τ = 0`: the small case, handled with `z ≤ -2000`
    have hz : z ≤ -2000 := hzero h0.symm
    rw [← h0]
    simp only [zpow_zero]
    have hzD : z / D ≤ -2000 / D := div_le_div_of_nonneg_right hz (le_of_lt hDpos)
    have hu0 : (0 : ℝ) ≤ 2000 / D := by positivity
    have hu1 : 2000 / D ≤ 1 := by rw [div_le_one hDpos]; linarith
    have h1 : Real.exp (z / D) ≤ 1 - 1000 / D := by
      calc Real.exp (z / D) ≤ Real.exp (-(2000 / D)) := by
            rw [show (-2000 : ℝ) / D = -(2000 / D) by ring] at hzD
            exact Real.exp_le_exp.mpr hzD
        _ ≤ 1 - (2000 / D) / 2 := exp_neg_le_one_sub_half_le_one_le_one hu0 hu1
        _ = 1 - 1000 / D := by ring
    have h4 : (4 : ℝ) / D ≤ 1000 / D :=
      div_le_div_of_nonneg_right (by norm_num) (le_of_lt hDpos)
    linarith
  · -- `1 ≤ τ`: the main estimate
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ τ := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, τ = (n : ℤ) :=
        ⟨τ.toNat, (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ τ)).symm⟩
      have hn1 : 1 ≤ n := by omega
      rw [hn, zpow_natCast]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    have hzD : z / D ≤ (τ : ℝ) * Real.log 2 - 4 / D := by
      have h := div_le_div_of_nonneg_right hmain (le_of_lt hDpos)
      have he : ((τ : ℝ) * Real.log 2 * D - 4) / D = (τ : ℝ) * Real.log 2 - 4 / D := by
        field_simp
      rwa [he] at h
    have hexp : Real.exp (z / D) ≤ Real.exp ((τ : ℝ) * Real.log 2 - 4 / D) :=
      Real.exp_le_exp.mpr hzD
    have hu0 : (0 : ℝ) ≤ 4 / D := by positivity
    have hu1 : 4 / D ≤ 1 := by rw [div_le_one hDpos]; linarith
    have heu : Real.exp (-(4 / D)) ≤ 1 - (4 / D) / 2 := exp_neg_le_one_sub_half_le_one_le_one hu0 hu1
    have hbound : Real.exp (z / D) ≤ (2 : ℝ) ^ τ * (1 - 2 / D) := by
      calc Real.exp (z / D) ≤ Real.exp ((τ : ℝ) * Real.log 2 - 4 / D) := hexp
        _ = Real.exp ((τ : ℝ) * Real.log 2) * Real.exp (-(4 / D)) := by
              rw [sub_eq_add_neg, Real.exp_add]
        _ = (2 : ℝ) ^ τ * Real.exp (-(4 / D)) := by rw [exp_intCast_mul_log_two τ hτ]
        _ ≤ (2 : ℝ) ^ τ * (1 - (4 / D) / 2) := mul_le_mul_of_nonneg_left heu (by positivity)
        _ = (2 : ℝ) ^ τ * (1 - 2 / D) := by ring
    have hkey : 4 / D ≤ (2 : ℝ) ^ τ * (2 / D) := by
      have h := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 / D)
      have heq : (2 : ℝ) * (2 / D) = 4 / D := by ring
      rwa [heq] at h
    have hmid : (2 : ℝ) ^ τ * (1 - 2 / D) + 4 / D ≤ (2 : ℝ) ^ τ := by
      nlinarith [hkey]
    linarith

end Work.Fx
