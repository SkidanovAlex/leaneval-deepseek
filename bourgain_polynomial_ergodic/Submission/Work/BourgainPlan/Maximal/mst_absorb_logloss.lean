import Mathlib

namespace Work.BourgainPlan.Maximal

/-- The polylogarithmic loss `(1 + log N)^{c_W}` at `N = 2^n` is absorbed by `n^{−γσ}` once `γσ ≥ α + c_W + 1`, leaving only the constant `(2(1+log 2))^{c_W} 2^α` in front of `(n+1)^{−α}`. -/
lemma mst_absorb_logloss (α cW γ σ : ℝ) (hα : 0 < α) (hcW : 0 < cW)
    (hγσ : α + cW + 1 ≤ γ*σ) (n : ℕ) (hn : 1 ≤ n) :
    (1 + Real.log ((2:ℝ)^n))^cW * (n:ℝ)^(-(γ*σ))
      ≤ ((1 + Real.log 2) * 2)^cW * 2^α * ((n:ℝ)+1)^(-α) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log ((2:ℝ)^n) = (n:ℝ) * Real.log 2 := by rw [Real.log_pow]
  rw [hlog]
  -- `1 + n log 2 ≤ (2 (1 + log 2)) n`
  have hconst : 1 + (n:ℝ) * Real.log 2 ≤ ((1 + Real.log 2) * 2) * (n:ℝ) := by
    nlinarith [hl2, hn1]
  have hbase : (0:ℝ) ≤ 1 + (n:ℝ) * Real.log 2 := by
    linarith [mul_pos hnpos hl2]
  have hnonneg : (0:ℝ) ≤ (1 + Real.log 2) * 2 := by linarith
  have hstep1 : (1 + (n:ℝ) * Real.log 2)^cW ≤ (((1 + Real.log 2) * 2) * (n:ℝ))^cW :=
    Real.rpow_le_rpow hbase hconst (le_of_lt hcW)
  rw [Real.mul_rpow hnonneg (le_of_lt hnpos)] at hstep1
  have hnmul : (n:ℝ)^cW * (n:ℝ)^(-(γ*σ)) = (n:ℝ)^(cW - γ*σ) := by
    rw [← Real.rpow_add hnpos]; ring_nf
  have hexp : cW - γ*σ ≤ -α - 1 := by linarith
  have hmono : (n:ℝ)^(cW - γ*σ) ≤ (n:ℝ)^(-α-1) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hn1pos : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hnp1pow : ((n:ℝ)+1)^α * ((n:ℝ)+1)^(-α) = 1 := by
    rw [← Real.rpow_add hn1pos, show α + -α = (0:ℝ) by ring, Real.rpow_zero]
  -- `n ^ (-α-1) * (n+1) ^ α ≤ 2 ^ α`
  have hkey : (n:ℝ)^(-α-1) * ((n:ℝ)+1)^α ≤ 2^α := by
    have hp1 : ((n:ℝ)+1)^α ≤ (2*(n:ℝ))^α := by
      refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hα)
      linarith
    have h2 : (2*(n:ℝ))^α = 2^α * (n:ℝ)^α := Real.mul_rpow (by norm_num) (le_of_lt hnpos)
    have h4 : (n:ℝ)^(-α-1) * (n:ℝ)^α = (n:ℝ)⁻¹ := by
      rw [← Real.rpow_add hnpos, show (-α-1) + α = (-(1:ℝ)) by ring,
        Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
    have h5 : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    calc (n:ℝ)^(-α-1) * ((n:ℝ)+1)^α
        ≤ (n:ℝ)^(-α-1) * (2*(n:ℝ))^α :=
          mul_le_mul_of_nonneg_left hp1 (Real.rpow_pos_of_pos hnpos (-α-1)).le
      _ = (n:ℝ)^(-α-1) * (2^α * (n:ℝ)^α) := by rw [h2]
      _ = 2^α * ((n:ℝ)^(-α-1) * (n:ℝ)^α) := by ring
      _ = 2^α * (n:ℝ)⁻¹ := by rw [h4]
      _ ≤ 2^α * 1 :=
          mul_le_mul_of_nonneg_left h5 (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α).le
      _ = 2^α := mul_one _
  have hfinal : (n:ℝ)^(-α-1) ≤ 2^α * ((n:ℝ)+1)^(-α) := by
    calc (n:ℝ)^(-α-1) = (n:ℝ)^(-α-1) * 1 := by ring
      _ = (n:ℝ)^(-α-1) * (((n:ℝ)+1)^α * ((n:ℝ)+1)^(-α)) := by rw [hnp1pow]
      _ = ((n:ℝ)^(-α-1) * ((n:ℝ)+1)^α) * ((n:ℝ)+1)^(-α) := by ring
      _ ≤ 2^α * ((n:ℝ)+1)^(-α) :=
          mul_le_mul_of_nonneg_right hkey (Real.rpow_pos_of_pos hn1pos (-α)).le
  have hcpos : (0:ℝ) < (1 + Real.log 2) * 2 := by linarith
  calc (1 + (n:ℝ) * Real.log 2)^cW * (n:ℝ)^(-(γ*σ))
      ≤ (((1 + Real.log 2) * 2)^cW * (n:ℝ)^cW) * (n:ℝ)^(-(γ*σ)) :=
        mul_le_mul_of_nonneg_right hstep1 (Real.rpow_pos_of_pos hnpos (-(γ*σ))).le
    _ = ((1 + Real.log 2) * 2)^cW * ((n:ℝ)^cW * (n:ℝ)^(-(γ*σ))) := by ring
    _ = ((1 + Real.log 2) * 2)^cW * (n:ℝ)^(cW - γ*σ) := by rw [hnmul]
    _ ≤ ((1 + Real.log 2) * 2)^cW * (n:ℝ)^(-α-1) :=
        mul_le_mul_of_nonneg_left hmono (Real.rpow_pos_of_pos hcpos cW).le
    _ ≤ ((1 + Real.log 2) * 2)^cW * (2^α * ((n:ℝ)+1)^(-α)) :=
        mul_le_mul_of_nonneg_left hfinal (Real.rpow_pos_of_pos hcpos cW).le
    _ = ((1 + Real.log 2) * 2)^cW * 2^α * ((n:ℝ)+1)^(-α) := by ring

end Work.BourgainPlan.Maximal
