import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

/-- For `0 < β ≤ 1` and `0 ≤ d ≤ δ`: `δ^(β-1) * d ≤ d^β`. -/
theorem rpow_sub_one_mul_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {δ d : ℝ} (hd0 : 0 ≤ d)
    (hdδ : d ≤ δ) : δ ^ (β - 1) * d ≤ d ^ β := by
  rcases lt_or_eq_of_le hd0 with hd | hd
  · have hδ : 0 < δ := lt_of_lt_of_le hd hdδ
    have h1 : 1 ≤ δ / d := (one_le_div hd).mpr hdδ
    have h2 : (δ / d) ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hd1 : d ^ β = d ^ (β - 1) * d := by
      have h := Real.rpow_add hd (β - 1) 1
      rw [show β - 1 + 1 = β by ring, Real.rpow_one] at h
      exact h
    have hdne : d ^ (β - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hd (β - 1))
    have hinner : (d ^ (β - 1))⁻¹ * (d ^ (β - 1) * d) = d := by
      rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    have h3 : (δ / d) ^ (β - 1) * d ^ β = δ ^ (β - 1) * d := by
      calc (δ / d) ^ (β - 1) * d ^ β
          = (δ ^ (β - 1) * (d ^ (β - 1))⁻¹) * (d ^ (β - 1) * d) := by
            rw [Real.div_rpow (le_of_lt hδ) (le_of_lt hd), hd1, div_eq_mul_inv]
        _ = δ ^ (β - 1) * ((d ^ (β - 1))⁻¹ * (d ^ (β - 1) * d)) := by rw [mul_assoc]
        _ = δ ^ (β - 1) * d := by rw [hinner]
    rw [← h3]
    calc (δ / d) ^ (β - 1) * d ^ β ≤ 1 * d ^ β :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hd0 β)
      _ = d ^ β := one_mul _
  · rw [← hd, mul_zero, Real.zero_rpow (ne_of_gt hβ)]

/-- The purely arithmetic core of the modulus estimate. -/
theorem wRateArithAux {F F' c c' δ δ' d L β : ℝ} (hL : 0 ≤ L)
    (hc' : 0 < c') (hcc : c' ≤ c)
    (hδ' : 0 ≤ δ') (hδδ : δ' ≤ δ) (hδ : 0 < δ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hcos : 2 / Real.pi * δ ≤ c)
    (hsub : c - c' ≤ d) (hdδ : d ≤ δ)
    (hF : |F - F'| ≤ L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
    (hF' : |F'| ≤ L * δ' ^ β * c' ^ 3 / 3) :
    |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'| ≤ 4 * L * d ^ β := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc
  have hcoef : 0 ≤ (c' ^ 3)⁻¹ - (c ^ 3)⁻¹ := by
    have hle : c' ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (le_of_lt hc') hcc 3
    exact sub_nonneg.mpr (inv_anti₀ (by positivity) hle)
  have hdec : |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'|
      ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := by
    have h1 : (c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'
        = (c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F')) := by ring
    rw [h1]
    have h2 : |(c ^ 3)⁻¹ * (F - F')| ≤ (c ^ 3)⁻¹ * |F - F'| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ c ^ 3))]
    have h3 : |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| ≤ ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := by
      rw [abs_mul, abs_of_nonneg hcoef]
    have hstep : |(c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))|
        ≤ |(c ^ 3)⁻¹ * (F - F')| + |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| := by
      have hh := abs_add_le ((c ^ 3)⁻¹ * (F - F')) (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))
      rwa [abs_neg] at hh
    calc |(c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))|
        ≤ |(c ^ 3)⁻¹ * (F - F')| + |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| := hstep
      _ ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := add_le_add h2 h3
  have hb1 : (c ^ 3)⁻¹ * |F - F'| ≤ (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have hb2 : ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'|
      ≤ ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3) :=
    mul_le_mul_of_nonneg_left hF' hcoef
  have hcomb : (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
      + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3)
      = (L / 3) * (δ ^ β + δ' ^ β) * (1 - (c' / c) ^ 3) := by
    field_simp
  have hA1 : δ ^ β + δ' ^ β ≤ 2 * δ ^ β := by
    have := Real.rpow_le_rpow hδ' hδδ hβ.le
    linarith
  have hA2 : 0 ≤ 1 - (c' / c) ^ 3 := by
    have hr0 : 0 ≤ c' / c := div_nonneg (le_of_lt hc') (le_of_lt hc)
    have hr : c' / c ≤ 1 := (div_le_one hc).mpr hcc
    have h : (c' / c) ^ 3 ≤ 1 := pow_le_one₀ hr0 hr
    linarith
  have hA3 : 1 - (c' / c) ^ 3 ≤ 3 * (c - c') / c := by
    have h1 : 1 - (c' / c) ^ 3 = (c ^ 3 - c' ^ 3) / c ^ 3 := by
      rw [div_pow]
      field_simp
    rw [h1]
    have h2 : c ^ 3 - c' ^ 3 ≤ 3 * (c - c') * c ^ 2 := by
      nlinarith [hcc, hc.le, hc'.le, mul_nonneg (le_of_lt hc') (sq_nonneg (c - c')),
        pow_nonneg (sub_nonneg.mpr hcc) 3]
    calc (c ^ 3 - c' ^ 3) / c ^ 3 ≤ (3 * (c - c') * c ^ 2) / c ^ 3 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 3 * (c - c') / c := by field_simp
  have hd0 : 0 ≤ d := le_trans (sub_nonneg.mpr hcc) hsub
  have h6 : δ ^ β / δ = δ ^ (β - 1) := by
    have h := Real.rpow_sub hδ β 1
    rw [Real.rpow_one] at h
    exact h.symm
  have hrp : δ ^ β / c ≤ (Real.pi / 2) * δ ^ (β - 1) := by
    have h1 : 1 / c ≤ Real.pi / (2 * δ) := by
      have h2 : 1 / c ≤ 1 / (2 / Real.pi * δ) := one_div_le_one_div_of_le (by positivity) hcos
      have h3 : 1 / (2 / Real.pi * δ) = Real.pi / (2 * δ) := by field_simp
      rwa [h3] at h2
    have h4 : δ ^ β / c ≤ δ ^ β * (Real.pi / (2 * δ)) := by
      have h4' := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hδ) β)
      rwa [mul_one_div] at h4'
    have h5 : δ ^ β * (Real.pi / (2 * δ)) = (Real.pi / 2) * δ ^ (β - 1) := by
      rw [show δ ^ β * (Real.pi / (2 * δ)) = Real.pi / 2 * (δ ^ β / δ) by field_simp, h6]
    rwa [h5] at h4
  calc |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'|
      ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := hdec
    _ ≤ (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
        + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3) := add_le_add hb1 hb2
    _ = (L / 3) * (δ ^ β + δ' ^ β) * (1 - (c' / c) ^ 3) := hcomb
    _ ≤ (L / 3) * (2 * δ ^ β) * (1 - (c' / c) ^ 3) := by
        have hL3 : 0 ≤ L / 3 := by positivity
        have := mul_le_mul_of_nonneg_left hA1 hL3
        exact mul_le_mul_of_nonneg_right this hA2
    _ ≤ (L / 3) * (2 * δ ^ β) * (3 * d / c) := by
        have h1 : 1 - (c' / c) ^ 3 ≤ 3 * d / c := by
          refine hA3.trans ?_
          exact div_le_div_of_nonneg_right (by linarith [hsub]) (le_of_lt hc)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * L * (δ ^ β / c) * d := by ring
    _ ≤ 2 * L * ((Real.pi / 2) * δ ^ (β - 1)) * d := by
        have h2 : (0 : ℝ) ≤ 2 * L := by linarith
        have := mul_le_mul_of_nonneg_left hrp h2
        exact mul_le_mul_of_nonneg_right this hd0
    _ = Real.pi * L * (δ ^ (β - 1) * d) := by ring
    _ ≤ Real.pi * L * d ^ β := mul_le_mul_of_nonneg_left
        (rpow_sub_one_mul_le hβ hβ1 hd0 hdδ) (by positivity)
    _ ≤ 4 * L * d ^ β := by
        have h3 : (0 : ℝ) ≤ L * d ^ β := mul_nonneg hL (Real.rpow_nonneg hd0 β)
        have hp := Real.pi_lt_four
        nlinarith

end Work.FTS_EllLimOK.ProducerH.H2
