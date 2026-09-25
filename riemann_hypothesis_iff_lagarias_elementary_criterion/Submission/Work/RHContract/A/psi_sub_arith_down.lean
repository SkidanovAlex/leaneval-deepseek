import Mathlib

namespace Work.RHContract.A

-- Pure real arithmetic (Mathlib only). With h := (43/100)·x^{3/4}, β ≤ 48/1000 and x ≥ 200 this is the
-- lower estimate for ψ(x) − x coming from the averaged explicit formula.
theorem psi_sub_arith_down (β x : ℝ) (hβ : β ≤ 48/1000) (hx : 200 ≤ x) :
    (43/100 * x ^ (3/4 : ℝ))/2 + Real.log (2 * Real.pi)
      + (β * (x ^ (3/2 : ℝ) + (x - 43/100 * x ^ (3/4 : ℝ)) ^ (3/2 : ℝ))
          + 1/x + 1/(x - 43/100 * x ^ (3/4 : ℝ))) / (43/100 * x ^ (3/4 : ℝ))
      ≤ 0.45 * x ^ (3/4 : ℝ) + 2 := by
  have hxpos : (0:ℝ) < x := by linarith
  set t : ℝ := x ^ (3/4 : ℝ) with ht
  have htpos : (0:ℝ) < t := by rw [ht]; exact Real.rpow_pos_of_pos hxpos _
  have h16 : (16:ℝ)^(3/4:ℝ) = 8 := by
    rw [show (16:ℝ) = 2^4 by norm_num, ← Real.rpow_natCast (2:ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have ht8 : (8:ℝ) ≤ t := by
    rw [ht]
    calc (8:ℝ) = (16:ℝ)^(3/4:ℝ) := h16.symm
      _ ≤ x^(3/4:ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have ht2 : (2:ℝ) ≤ t := by linarith
  have htx : t ≤ x := by
    rw [ht]
    have h : x^(3/4:ℝ) ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    simpa [Real.rpow_one] using h
  have hsub_le : x - 43/100 * t ≤ x := by linarith
  have hsub_nonneg : (0:ℝ) ≤ x - 43/100 * t := by
    have h1 : 43/100 * t ≤ 43/100 * x := by linarith [htx]
    have h2 : (43/100:ℝ) * x ≤ x := by linarith [hxpos.le]
    linarith
  have hsub_ge : (100:ℝ) ≤ x - 43/100 * t := by
    have h1 : 43/100 * t ≤ 43/100 * x := by linarith [htx]
    linarith
  have hu_nonneg : (0:ℝ) ≤ x^(3/2:ℝ) := Real.rpow_nonneg hxpos.le _
  have hv_nonneg : (0:ℝ) ≤ (x - 43/100 * t)^(3/2:ℝ) := Real.rpow_nonneg hsub_nonneg _
  have hv_le_u : (x - 43/100 * t)^(3/2:ℝ) ≤ x^(3/2:ℝ) :=
    Real.rpow_le_rpow hsub_nonneg hsub_le (by norm_num)
  have hx32 : x^(3/2:ℝ) = t * t := by
    rw [ht]
    rw [show (3/2:ℝ) = 3/4 + 3/4 by norm_num, Real.rpow_add hxpos]
  have hN_le : β * (x^(3/2:ℝ) + (x - 43/100 * t)^(3/2:ℝ)) + 1/x + 1/(x - 43/100*t)
      ≤ (12/125:ℝ) * x^(3/2:ℝ) + 3/200 := by
    have hsum_nonneg : 0 ≤ x^(3/2:ℝ) + (x - 43/100 * t)^(3/2:ℝ) := by linarith
    have hstep1 : β * (x^(3/2:ℝ) + (x - 43/100*t)^(3/2:ℝ))
        ≤ (48/1000:ℝ) * (x^(3/2:ℝ) + (x - 43/100*t)^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right hβ hsum_nonneg
    have hstep2 : (48/1000:ℝ) * (x^(3/2:ℝ) + (x - 43/100*t)^(3/2:ℝ)) ≤ (12/125:ℝ) * x^(3/2:ℝ) := by
      nlinarith [hv_le_u, hu_nonneg]
    have hx1 : 1/x ≤ 1/200 := one_div_le_one_div_of_le (by norm_num) hx
    have hx2 : 1/(x - 43/100*t) ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) hsub_ge
    linarith
  have hDpos : (0:ℝ) < 43/100 * t := by positivity
  have hND : (β * (x^(3/2:ℝ) + (x - 43/100 * t)^(3/2:ℝ)) + 1/x + 1/(x - 43/100*t))/(43/100 * t)
      ≤ 48/215 * t + 3/(86 * t) := by
    have h1 := div_le_div_of_nonneg_right hN_le hDpos.le
    have h2 : ((12/125:ℝ)*x^(3/2:ℝ) + 3/200)/(43/100 * t) = 48/215*t + 3/(86*t) := by
      rw [hx32]; field_simp; ring
    linarith
  have hfinal : (43/100 * t)/2 + Real.log (2*Real.pi) + (48/215*t + 3/(86*t)) ≤ 0.45 * t + 2 := by
    have hlog : Real.log (2 * Real.pi) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2, Real.pi_pos, Real.exp_pos 1]
    have h3 : 3/(86*t) ≤ (101/8600:ℝ)*t := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 86*t)]
      nlinarith [ht2]
    linarith [hlog, h3]
  linarith [hND, hfinal]

end Work.RHContract.A
