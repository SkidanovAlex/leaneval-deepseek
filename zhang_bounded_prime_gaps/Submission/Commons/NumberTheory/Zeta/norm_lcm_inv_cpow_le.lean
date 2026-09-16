import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Zeta

theorem norm_lcm_inv_cpow_le {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (d d' : ℕ) :
    ‖(((Nat.lcm d d' : ℕ)) : ℂ)⁻¹ * (d : ℂ) ^ (-a) * (d' : ℂ) ^ (-b)‖
      ≤ (Nat.gcd d d' : ℝ) * (d : ℝ) ^ (-(1 + a.re)) * (d' : ℝ) ^ (-(1 + b.re)) := by
  have ha' : (-a).re ≠ 0 := by rw [Complex.neg_re]; exact neg_ne_zero.mpr ha.ne'
  have hb' : (-b).re ≠ 0 := by rw [Complex.neg_re]; exact neg_ne_zero.mpr hb.ne'
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_re_ne_zero d ha',
      Complex.norm_natCast_cpow_of_re_ne_zero d' hb']
  simp only [Complex.neg_re]
  by_cases hd : d = 0
  · subst hd
    simp only [Nat.lcm_zero_left, Nat.gcd_zero_left, Nat.cast_zero]
    rw [Real.zero_rpow (neg_ne_zero.mpr ha.ne'), Real.zero_rpow (by linarith : -(1 + a.re) ≠ 0)]
    simp
  · by_cases hd' : d' = 0
    · subst hd'
      simp only [Nat.lcm_zero_right, Nat.gcd_zero_right, Nat.cast_zero]
      rw [Real.zero_rpow (neg_ne_zero.mpr hb.ne'), Real.zero_rpow (by linarith : -(1 + b.re) ≠ 0)]
      simp
    · have hDpos : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hD'pos : (0:ℝ) < d' := by exact_mod_cast Nat.pos_of_ne_zero hd'
      have hD : (d:ℝ) ≠ 0 := ne_of_gt hDpos
      have hD' : (d':ℝ) ≠ 0 := ne_of_gt hD'pos
      have hGL : (Nat.gcd d d' : ℝ) * (Nat.lcm d d' : ℝ) = (d:ℝ) * (d':ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d d'
      have hGLne : (Nat.gcd d d' : ℝ) * (Nat.lcm d d' : ℝ) ≠ 0 := by
        rw [hGL]; exact mul_ne_zero hD hD'
      have hG : (Nat.gcd d d' : ℝ) ≠ 0 := left_ne_zero_of_mul hGLne
      have key : (Nat.gcd d d' : ℝ) * (d:ℝ)⁻¹ * (d':ℝ)⁻¹ = (Nat.lcm d d' : ℝ)⁻¹ := by
        have h2 : ((Nat.gcd d d' : ℝ) * (Nat.lcm d d' : ℝ))⁻¹
            = ((d:ℝ) * (d':ℝ))⁻¹ := by rw [hGL]
        rw [mul_inv, mul_inv] at h2
        rw [mul_assoc, ← h2, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
      have eD : (d:ℝ) ^ (-(1 + a.re)) = (d:ℝ)⁻¹ * (d:ℝ) ^ (-a.re) := by
        rw [show -(1 + a.re) = -1 + (-a.re) by ring, Real.rpow_add hDpos, Real.rpow_neg_one]
      have eD' : (d':ℝ) ^ (-(1 + b.re)) = (d':ℝ)⁻¹ * (d':ℝ) ^ (-b.re) := by
        rw [show -(1 + b.re) = -1 + (-b.re) by ring, Real.rpow_add hD'pos, Real.rpow_neg_one]
      apply le_of_eq
      rw [eD, eD', ← key]
      ring

end Commons.NumberTheory.Zeta