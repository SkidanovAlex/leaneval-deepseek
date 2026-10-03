import Mathlib
import Submission.Work.Pert.Basic

/-!
# The estimate `τ_f(w) + 1/w = O(1/|w|)` (Shishikura, PERT area)

With `τ_f(w) = σ/(1 - e^{-2πiαw})` (`Work.Pert.tauC`) and `z = 2πiαw`, the Laurent expansion of
`1/(1-e^{-z})` at the pole `z = 0` reads

  `1/(1 - e^{-z}) = 1/z + 1/2 + Ψ(z)`,  `Ψ(z) = 1/(1-e^{-z}) - 1/z - 1/2`,

and `Ψ(z) = O(z)`.  Hence

  `τ_f(w) + 1/w = (σ/α + 2πi)/(2πi w) + (σ/2 + σ·Ψ(z))`,

whose norm is bounded by `‖σ/α + 2πi‖/(2π m) + (3/2)‖σ‖` for `m ≤ ‖w‖`, `2π‖α‖‖w‖ ≤ 1/2`.
Since `‖σ‖ ≤ ‖α‖(‖σ/α + 2πi‖ + 2π)` this gives the stated estimate.

The analytic input is the cubic Taylor residual `norm_exp_cubic_residual`; the rest is the
lower bound `‖1 - e^{-z}‖ ≥ ‖z‖/2` for `‖z‖ ≤ 1/2` (from `Complex.norm_exp_sub_one_sub_id_le`)
and elementary real arithmetic.
-/

namespace Work.Pert

open Complex

noncomputable section

/-- Cubic Taylor residual of `e^{-z}`: for `‖z‖ ≤ 1/2`,
`z - 2 + (z+2)e^{-z} = z³/6 - z⁴/12 + z⁵/24 + (z+2)R₅(z)` with `‖R₅(z)‖ ≤ 2‖z‖⁵`,
hence `‖z - 2 + (z+2)e^{-z}‖ ≤ 2‖z‖³`. -/
theorem norm_exp_cubic_residual (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖z - 2 + (z + 2) * Complex.exp (-z)‖ ≤ 2 * ‖z‖ ^ 3 := by
  have hez : Real.exp ‖z‖ ≤ 2 := by
    have h1 : Real.exp ‖(z : ℂ)‖ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hz
    have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have h3 : Real.exp (1 : ℝ) = Real.exp (1 / 2) * Real.exp (1 / 2) := by
        rw [← Real.exp_add]; norm_num
      have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      nlinarith [Real.exp_one_lt_three, h3]
    linarith
  have hT : (∑ m ∈ Finset.range 5, (-z) ^ m / m.factorial) = 1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have hR : ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)‖ ≤ ‖z‖ ^ 5 * 2 := by
    have h0 := Complex.norm_exp_sub_sum_le_norm_mul_exp (-z) 5
    rw [norm_neg] at h0
    rw [hT] at h0
    calc ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)‖ ≤ ‖z‖ ^ 5 * Real.exp ‖z‖ := h0
      _ ≤ ‖z‖ ^ 5 * 2 := mul_le_mul_of_nonneg_left hez (pow_nonneg (norm_nonneg z) 5)
  have hkey : z - 2 + (z + 2) * Complex.exp (-z)
      = (z ^ 3 / 6 - z ^ 4 / 12 + z ^ 5 / 24)
        + (z + 2) * (Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)) := by ring
  rw [hkey]
  have e3 : ‖z ^ 3 / 6‖ = ‖z‖ ^ 3 / 6 := by rw [norm_div, norm_pow]; norm_num
  have e4 : ‖z ^ 4 / 12‖ = ‖z‖ ^ 4 / 12 := by rw [norm_div, norm_pow]; norm_num
  have e5 : ‖z ^ 5 / 24‖ = ‖z‖ ^ 5 / 24 := by rw [norm_div, norm_pow]; norm_num
  calc ‖(z ^ 3 / 6 - z ^ 4 / 12 + z ^ 5 / 24)
          + (z + 2) * (Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24))‖
      ≤ ‖z ^ 3 / 6 - z ^ 4 / 12 + z ^ 5 / 24‖
        + ‖(z + 2) * (Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24))‖ := norm_add_le _ _
    _ ≤ (‖z‖ ^ 3 / 6 + ‖z‖ ^ 4 / 12 + ‖z‖ ^ 5 / 24) + (‖z‖ + 2) * (‖z‖ ^ 5 * 2) := by
        apply add_le_add
        · have h1 := norm_add_le (z ^ 3 / 6 - z ^ 4 / 12) (z ^ 5 / 24)
          have h2 := norm_sub_le (z ^ 3 / 6) (z ^ 4 / 12)
          linarith [h1, h2, e3, e4, e5]
        · rw [norm_mul]
          have hz2 : ‖z + 2‖ ≤ ‖z‖ + 2 := by
            simpa using norm_add_le z (2 : ℂ)
          exact mul_le_mul hz2 hR (norm_nonneg _) (by positivity)
    _ ≤ 2 * ‖z‖ ^ 3 := by
        have h0 : 0 ≤ ‖z‖ := norm_nonneg z
        have ht2 : ‖z‖ ^ 2 ≤ 1 / 4 := by nlinarith [hz, h0]
        have h4 : ‖z‖ ^ 4 ≤ ‖z‖ ^ 3 / 2 := by nlinarith [hz, h0, pow_nonneg h0 3]
        have h5 : ‖z‖ ^ 5 ≤ ‖z‖ ^ 3 / 4 := by nlinarith [ht2, h0, pow_nonneg h0 3]
        have h6 : ‖z‖ ^ 6 ≤ ‖z‖ ^ 3 / 8 := by nlinarith [ht2, h0, pow_nonneg h0 3]
        nlinarith [h4, h5, h6, h0]

/-- For `‖z‖ ≤ 1/2` the quantity `1 - e^{-z}` is bounded below by `‖z‖/2`
(from the order-two Taylor bound `‖e^{-z} - 1 + z‖ ≤ ‖z‖²`). -/
theorem norm_one_sub_exp_neg_ge (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖z‖ / 2 ≤ ‖1 - Complex.exp (-z)‖ := by
  have hle1 : ‖(-z : ℂ)‖ ≤ 1 := by rw [norm_neg]; linarith
  have hR : ‖Complex.exp (-z) - 1 + z‖ ≤ ‖z‖ ^ 2 := by
    have h1 := Complex.norm_exp_sub_one_sub_id_le (x := -z) hle1
    simpa using h1
  have htri : ‖z‖ ≤ ‖1 - Complex.exp (-z)‖ + ‖Complex.exp (-z) - 1 + z‖ := by
    have hh := norm_add_le (1 - Complex.exp (-z)) (Complex.exp (-z) - 1 + z)
    have heq2 : (1 - Complex.exp (-z)) + (Complex.exp (-z) - 1 + z) = z := by ring
    rwa [heq2] at hh
  have hz2 : ‖z‖ * ‖z‖ ≤ 1 / 2 * ‖z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg z)
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith [hz2, norm_nonneg z, hz]
  linarith

/-- The Laurent expansion of `1/(1-e^{-z})` at `z = 0` to first order: the residual
`Ψ(z) = 1/(1-e^{-z}) - 1/z - 1/2` satisfies `‖Ψ(z)‖ ≤ 2‖z‖` for `0 < ‖z‖ ≤ 1/2`.

Indeed `2z(1-e^{-z})Ψ(z) = z - 2 + (z+2)e^{-z}` (bounded by `2‖z‖³`, `exp_cubic_residual`) and
`‖1 - e^{-z}‖ ≥ ‖z‖/2`. -/
theorem norm_psi_le (z : ℂ) (hz : z ≠ 0) (h : ‖z‖ ≤ 1 / 2) :
    ‖1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2‖ ≤ 2 * ‖z‖ := by
  have hge : ‖z‖ / 2 ≤ ‖1 - Complex.exp (-z)‖ := norm_one_sub_exp_neg_ge z h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hne : (1 - Complex.exp (-z)) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hge; linarith
  have hident : 1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2
      = (z - 2 + (z + 2) * Complex.exp (-z)) / (2 * z * (1 - Complex.exp (-z))) := by
    field_simp
    ring
  rw [hident, norm_div, norm_mul, norm_mul]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2n]
  have hden : 0 < 2 * ‖z‖ * ‖1 - Complex.exp (-z)‖ := by positivity
  rw [div_le_iff₀ hden]
  have key3 : ‖z‖ ^ 2 ≤ 2 * ‖z‖ * ‖1 - Complex.exp (-z)‖ := by
    have key2 : 2 * ‖z‖ * (‖z‖ / 2) ≤ 2 * ‖z‖ * ‖1 - Complex.exp (-z)‖ :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    nlinarith [key2]
  have key4 : 2 * ‖z‖ * ‖z‖ ^ 2 ≤ 2 * ‖z‖ * (2 * ‖z‖ * ‖1 - Complex.exp (-z)‖) :=
    mul_le_mul_of_nonneg_left key3 (by positivity)
  linarith [norm_exp_cubic_residual z h, key4]

/-- Shishikura (A.1.7)(ii)-type estimate: for `0 < m ≤ ‖w‖` and `2π‖α‖‖w‖ ≤ 1/2`,

  `‖τ_f(w) + 1/w‖ ≤ ‖σ/α + 2πi‖/(π m) + (2π)²‖α‖/π`. -/
theorem tauC_add_inv_le (σ α w : ℂ) (hα : α ≠ 0) (hw : w ≠ 0) {m : ℝ} (hm : 0 < m)
    (hwm : m ≤ ‖w‖) (hsmall : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2) :
    ‖Work.Pert.tauC σ α w + 1 / w‖ ≤
      ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m) + (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi := by
  rw [Work.Pert.tauC]
  set z : ℂ := 2 * Real.pi * Complex.I * α * w with hzdef
  have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hI
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    exact mul_ne_zero (mul_ne_zero h2pi hα) hw
  have hznorm : ‖z‖ = 2 * Real.pi * ‖α‖ * ‖w‖ := by
    rw [hzdef, norm_mul, norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
  have hzle : ‖z‖ ≤ 1 / 2 := by rw [hznorm]; exact hsmall
  have hne : (1 - Complex.exp (-z)) ≠ 0 := by
    have hge := norm_one_sub_exp_neg_ge z hzle
    intro h0; rw [h0, norm_zero] at hge; linarith [norm_pos_iff.mpr hz0]
  have hPsi : ‖1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2‖ ≤ 2 * ‖z‖ :=
    norm_psi_le z hz0 hzle
  have hsecond : σ / z + 1 / w = (σ / α + 2 * Real.pi * Complex.I) / (2 * Real.pi * Complex.I * w) := by
    rw [hzdef]
    have hden2 : (2 : ℂ) * Real.pi * Complex.I * w ≠ 0 := mul_ne_zero h2pi hw
    rw [eq_div_iff hden2]
    field_simp
  have hmain : σ / (1 - Complex.exp (-z)) + 1 / w
      = (σ / α + 2 * Real.pi * Complex.I) / (2 * Real.pi * Complex.I * w)
        + (σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / 2) := by
    have h1 : σ / (1 - Complex.exp (-z))
        = σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / z + σ / 2 := by ring
    rw [h1]
    have h2 : σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / z + σ / 2 + 1 / w
        = (σ / z + 1 / w) + (σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / 2) := by ring
    rw [h2, hsecond]
  rw [hmain]
  have hdennorm : ‖(2 : ℂ) * Real.pi * Complex.I * w‖ = 2 * Real.pi * ‖w‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
  have hA : ‖(σ / α + 2 * Real.pi * Complex.I) / (2 * Real.pi * Complex.I * w)‖
      ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) := by
    rw [norm_div, hdennorm]
    gcongr
  have hB : ‖σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / 2‖ ≤ (3 / 2) * ‖σ‖ := by
    have h1 : ‖σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2)‖ ≤ ‖σ‖ * (2 * ‖z‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hPsi (norm_nonneg σ)
    have h2 : ‖σ / 2‖ = ‖σ‖ / 2 := by rw [norm_div]; norm_num
    have h3 := norm_add_le (σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2)) (σ / 2)
    rw [h2] at h3
    have h4 : ‖σ‖ * (2 * ‖z‖) ≤ ‖σ‖ := by nlinarith [norm_nonneg σ, hzle]
    linarith
  have hcomb : ‖(σ / α + 2 * Real.pi * Complex.I) / (2 * Real.pi * Complex.I * w)
          + (σ * (1 / (1 - Complex.exp (-z)) - 1 / z - 1 / 2) + σ / 2)‖
        ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) + (3 / 2) * ‖σ‖ :=
    (norm_add_le _ _).trans (add_le_add hA hB)
  have harith : ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) + (3 / 2) * ‖σ‖
      ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m)
          + (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi := by
    have hAm : 3 * Real.pi * ‖α‖ * m ≤ 1 := by
      have h1 : 2 * Real.pi * ‖α‖ * m ≤ 2 * Real.pi * ‖α‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_left hwm (by positivity)
      nlinarith [h1, hsmall, Real.pi_pos, norm_nonneg α]
    have hkey : (3 / 2) * ‖α‖ ≤ 1 / (2 * Real.pi * m) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hAm]
    have hsa : ‖σ / α‖ ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi := by
      have heq : σ / α = (σ / α + 2 * Real.pi * Complex.I) + (-(2 * Real.pi * Complex.I)) := by ring
      calc ‖σ / α‖ = ‖(σ / α + 2 * Real.pi * Complex.I) + (-(2 * Real.pi * Complex.I))‖ :=
              congrArg norm heq
        _ ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ + ‖-(2 * Real.pi * Complex.I)‖ := norm_add_le _ _
        _ = ‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi := by
            congr 1
            rw [norm_neg, norm_mul, norm_mul]
            simp [Complex.norm_I, Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
    have hσ : ‖σ‖ ≤ ‖α‖ * (‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi) := by
      have heq : σ = α * (σ / α) := (mul_div_cancel₀ σ hα).symm
      calc ‖σ‖ = ‖α * (σ / α)‖ := congrArg norm heq
        _ = ‖α‖ * ‖σ / α‖ := norm_mul α _
        _ ≤ ‖α‖ * (‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi) :=
            mul_le_mul_of_nonneg_left hsa (norm_nonneg α)
    have hce : (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi = 4 * Real.pi * ‖α‖ := by
      field_simp
      ring
    rw [hce]
    have h3 : (3 / 2) * ‖α‖ * ‖σ / α + 2 * Real.pi * Complex.I‖
        ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) := by
      have h4 : (3 / 2) * ‖α‖ * ‖σ / α + 2 * Real.pi * Complex.I‖
          ≤ (1 / (2 * Real.pi * m)) * ‖σ / α + 2 * Real.pi * Complex.I‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      have h5 : (1 / (2 * Real.pi * m)) * ‖σ / α + 2 * Real.pi * Complex.I‖
          = ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) := by ring
      linarith [h4, h5]
    have h6 : 3 * Real.pi * ‖α‖ ≤ 4 * Real.pi * ‖α‖ := by nlinarith [norm_nonneg α, Real.pi_pos]
    have h7 : ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m)
        + ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m)
        = ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m) := by
      field_simp
      ring
    have hexp : (3 / 2) * (‖α‖ * (‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi))
        = (3 / 2) * ‖α‖ * ‖σ / α + 2 * Real.pi * Complex.I‖ + 3 * Real.pi * ‖α‖ := by ring
    have h1 : ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m) + (3 / 2) * ‖σ‖
        ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (2 * Real.pi * m)
          + (3 / 2) * (‖α‖ * (‖σ / α + 2 * Real.pi * Complex.I‖ + 2 * Real.pi)) := by
      linarith [hσ]
    rw [hexp] at h1
    linarith [h1, h3, h6, h7]
  exact le_trans hcomb harith

end

end Work.Pert
