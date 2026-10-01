import Mathlib

namespace Work.ZeroDensity.Ingham


/-- For `u ≥ log 2` and `1/2 ≤ σ ≤ 1`, `u ^ (1 - σ) ≤ u + log 2`. -/
private lemma logPowKey (u σ : ℝ) (hu : Real.log 2 ≤ u) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) :
    u ^ (1 - σ) ≤ u + Real.log 2 := by
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2nn : 0 ≤ Real.log 2 := by linarith
  by_cases h : u ≤ 1
  · have hu0 : 0 ≤ u := le_trans hlog2nn hu
    have h1σ : 0 ≤ 1 - σ := by linarith
    have hle1 : u ^ (1 - σ) ≤ 1 := Real.rpow_le_one hu0 h h1σ
    linarith
  · have hu1 : 1 ≤ u := le_of_lt (not_le.mp h)
    have hexp : 1 - σ ≤ 1 := by linarith
    have hle : u ^ (1 - σ) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hexp
    rw [Real.rpow_one] at hle
    linarith

/-- `u ^ (8 - 8σ) ≤ (u + log 2)^8` for `u ≥ log 2`, `1/2 ≤ σ ≤ 1`. -/
private lemma logPow8Key (u σ : ℝ) (hu : Real.log 2 ≤ u) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) :
    u ^ (8 - 8 * σ) ≤ (u + Real.log 2) ^ 8 := by
  have hlog2nn : 0 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu0 : 0 ≤ u := le_trans hlog2nn hu
  have hstep : u ^ (1 - σ) ≤ u + Real.log 2 := logPowKey u σ hu hσ1 hσ2
  have hnn : 0 ≤ u ^ (1 - σ) := Real.rpow_nonneg hu0 _
  have hpow : (u ^ (1 - σ)) ^ 8 ≤ (u + Real.log 2) ^ 8 := pow_le_pow_left₀ hnn hstep 8
  have hEq : u ^ (8 - 8 * σ) = (u ^ (1 - σ)) ^ 8 := by
    rw [show (8 : ℝ) - 8 * σ = (1 - σ) * ((8 : ℕ) : ℝ) by ring, Real.rpow_mul hu0,
      Real.rpow_natCast]
  rw [hEq]
  exact hpow

/-- Term estimate for the `n`-part: `e^{-2x/Y} x^{2-2σ} ≤ Y^{2-2σ} (log (2BH))^8`
when `x ≤ Y (log (BH))^4`. -/
private lemma expMulNpowBound (σ Y x B H : ℝ) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1)
    (hY : 1 ≤ Y) (hBH : 2 ≤ B * H) (hx1 : 1 ≤ x) (hxL : x ≤ Y * (Real.log (B * H)) ^ 4) :
    Real.exp (-(2 * x / Y)) * x ^ (2 - 2 * σ) ≤ Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 := by
  have hY0 : 0 ≤ Y := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hBHpos : 0 < B * H := by linarith
  have hlogBH0 : 0 ≤ Real.log (B * H) := Real.log_nonneg (by linarith)
  have hlog2BH : Real.log (2 * (B * H)) = Real.log 2 + Real.log (B * H) :=
    Real.log_mul (by norm_num) (ne_of_gt hBHpos)
  have hE1 : Real.exp (-(2 * x / Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * x / Y := div_nonneg (by linarith) (by linarith)
    linarith
  have hxpow0 : 0 ≤ x ^ (2 - 2 * σ) := Real.rpow_nonneg hx0 _
  have hstep1 : Real.exp (-(2 * x / Y)) * x ^ (2 - 2 * σ) ≤ x ^ (2 - 2 * σ) := by
    calc Real.exp (-(2 * x / Y)) * x ^ (2 - 2 * σ) ≤ 1 * x ^ (2 - 2 * σ) :=
          mul_le_mul_of_nonneg_right hE1 hxpow0
      _ = x ^ (2 - 2 * σ) := by rw [one_mul]
  have h2σ : 0 ≤ 2 - 2 * σ := by linarith
  have hstep2 : x ^ (2 - 2 * σ) ≤ (Y * (Real.log (B * H)) ^ 4) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow hx0 hxL h2σ
  have hlogBH4nn : 0 ≤ (Real.log (B * H)) ^ 4 := pow_nonneg hlogBH0 4
  have hsplit : (Y * (Real.log (B * H)) ^ 4) ^ (2 - 2 * σ)
      = Y ^ (2 - 2 * σ) * (Real.log (B * H)) ^ (8 - 8 * σ) := by
    rw [Real.mul_rpow hY0 hlogBH4nn]
    congr 1
    rw [← Real.rpow_natCast (Real.log (B * H)) 4, ← Real.rpow_mul hlogBH0]
    congr 1
    ring
  have hlogBHge : Real.log 2 ≤ Real.log (B * H) := Real.log_le_log (by norm_num) (by linarith)
  have hlog8 : (Real.log (B * H)) ^ (8 - 8 * σ) ≤ (Real.log (2 * (B * H))) ^ 8 := by
    have h := logPow8Key (Real.log (B * H)) σ hlogBHge hσ1 hσ2
    rw [hlog2BH]
    rw [add_comm (Real.log (B * H)) (Real.log 2)] at h
    exact h
  calc Real.exp (-(2 * x / Y)) * x ^ (2 - 2 * σ)
      ≤ x ^ (2 - 2 * σ) := hstep1
    _ ≤ (Y * (Real.log (B * H)) ^ 4) ^ (2 - 2 * σ) := hstep2
    _ = Y ^ (2 - 2 * σ) * (Real.log (B * H)) ^ (8 - 8 * σ) := hsplit
    _ ≤ Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 :=
        mul_le_mul_of_nonneg_left hlog8 (Real.rpow_nonneg hY0 _)

/-- Term estimate for the `H`-part: `e^{-2x/Y} x^{1-2σ} H ≤ H K^{1-2σ}` when `K ≤ x`. -/
private lemma expMulRpowNpowLe (σ Y x K H : ℝ) (hσ1 : 1 / 2 ≤ σ)
    (hKpos : 0 < K) (hKx : K ≤ x) (hYpos : 0 < Y) (hx0 : 0 ≤ x) (hH0 : 0 ≤ H) :
    Real.exp (-(2 * x / Y)) * x ^ (1 - 2 * σ) * H ≤ H * K ^ (1 - 2 * σ) := by
  have hE1 : Real.exp (-(2 * x / Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * x / Y := div_nonneg (by linarith) (by linarith)
    linarith
  have hexp : 1 - 2 * σ ≤ 0 := by linarith
  have hKxpow : x ^ (1 - 2 * σ) ≤ K ^ (1 - 2 * σ) :=
    Real.rpow_le_rpow_of_nonpos hKpos hKx hexp
  have hxpow0 : 0 ≤ x ^ (1 - 2 * σ) := Real.rpow_nonneg hx0 _
  have h1 : Real.exp (-(2 * x / Y)) * x ^ (1 - 2 * σ) ≤ K ^ (1 - 2 * σ) := by
    calc Real.exp (-(2 * x / Y)) * x ^ (1 - 2 * σ) ≤ 1 * x ^ (1 - 2 * σ) :=
          mul_le_mul_of_nonneg_right hE1 hxpow0
      _ = x ^ (1 - 2 * σ) := by rw [one_mul]
      _ ≤ K ^ (1 - 2 * σ) := hKxpow
  calc Real.exp (-(2 * x / Y)) * x ^ (1 - 2 * σ) * H ≤ K ^ (1 - 2 * σ) * H :=
        mul_le_mul_of_nonneg_right h1 hH0
    _ = H * K ^ (1 - 2 * σ) := by ring

theorem zetaTailTermLogWeightSelf (K L : ℕ) (σ Y H B : ℝ) (n : ℕ)
    (hK : 1 ≤ K) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) (hY : 1 ≤ Y) (hH : 2 ≤ H) (hB : 1 ≤ B)
    (hL : (L : ℝ) ≤ Y * (Real.log (B * H)) ^ 4) (hn : n ∈ Finset.Ioc K L) :
    ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ))
        * (H + (n : ℝ)) * (1 + Real.log (n : ℝ)) ^ 3
      ≤ ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹ *
        (H * (K : ℝ) ^ (1 - 2 * σ)
          + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) := by
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hKn, hnL⟩ := hn
  have hn2 : 2 ≤ n := by omega
  have hx0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hY0 : (0 : ℝ) < Y := by linarith
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hBH : (2 : ℝ) ≤ B * H := by
    nlinarith [mul_le_mul hB hH (by norm_num : (0:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ B)]
  have hlogBH0 : 0 ≤ Real.log (B * H) := Real.log_nonneg (by linarith)
  have hxL : (n : ℝ) ≤ Y * (Real.log (B * H)) ^ 4 := by
    have : (n : ℝ) ≤ (L : ℝ) := by exact_mod_cast hnL
    linarith
  have hterm1 : Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * H
      ≤ H * (K : ℝ) ^ (1 - 2 * σ) :=
    expMulRpowNpowLe σ Y (n : ℝ) (K : ℝ) H hσ1 (by exact_mod_cast (by omega : 0 < K))
      (by exact_mod_cast (le_of_lt hKn)) hY0 hx0 hH0
  have hterm2 : Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (2 - 2 * σ)
      ≤ Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 :=
    expMulNpowBound σ Y (n : ℝ) B H hσ1 hσ2 hY hBH hx1 hxL
  have hxpowx : (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ) = (n : ℝ) ^ (2 - 2 * σ) := by
    calc (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ) = (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 - 2 * σ) + 1) := by rw [Real.rpow_add hxpos]
      _ = (n : ℝ) ^ (2 - 2 * σ) := by congr 1; ring
  have hcore2 : Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * (H + (n : ℝ))
      ≤ H * (K : ℝ) ^ (1 - 2 * σ) + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 := by
    calc Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * (H + (n : ℝ))
        = Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * H
          + Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ) := by ring
      _ ≤ H * (K : ℝ) ^ (1 - 2 * σ) + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 :=
          add_le_add hterm1 (by
            calc Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ)
                = Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (2 - 2 * σ) := by
                  rw [mul_assoc, hxpowx]
              _ ≤ Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 := hterm2)
  have hrpow : (n : ℝ) ^ (-(2 * σ)) = ((n : ℝ))⁻¹ * (n : ℝ) ^ (1 - 2 * σ) := by
    rw [show -(2 * σ) = (-1 : ℝ) + (1 - 2 * σ) by ring]
    rw [Real.rpow_add hxpos]
    rw [Real.rpow_neg_one]
  have hcore : Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ)) * (H + (n : ℝ))
      ≤ ((n : ℝ))⁻¹ * (H * (K : ℝ) ^ (1 - 2 * σ)
          + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) := by
    calc Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ)) * (H + (n : ℝ))
        = ((n : ℝ))⁻¹ * (Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (1 - 2 * σ)
            * (H + (n : ℝ))) := by rw [hrpow]; ring
      _ ≤ ((n : ℝ))⁻¹ * (H * (K : ℝ) ^ (1 - 2 * σ)
            + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) :=
          mul_le_mul_of_nonneg_left hcore2 (inv_nonneg.mpr hx0)
  have hlog_nn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hDW : (0 : ℝ) ≤ ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 3)
  calc ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ))
        * (H + (n : ℝ)) * (1 + Real.log (n : ℝ)) ^ 3
      = ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3
          * (Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ)) * (H + (n : ℝ))) := by ring
    _ ≤ ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3
          * (((n : ℝ))⁻¹ * (H * (K : ℝ) ^ (1 - 2 * σ)
              + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8)) :=
        mul_le_mul_of_nonneg_left hcore hDW
    _ = ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹
          * (H * (K : ℝ) ^ (1 - 2 * σ)
            + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) := by ring

end Work.ZeroDensity.Ingham
