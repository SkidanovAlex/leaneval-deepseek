import Mathlib
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_le_max
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_sq_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

/-- The elementary trigonometric inequality behind the upper half of the transit
strip: for `0 ≤ θ ≤ π/2` and `c ≤ θ` one has `c·cos θ ≤ sin θ`.

It is the tangent inequality `t ≤ tan t` in the form we need.  Indeed for
`cos θ > 0` we have `θ ≤ tan θ = sin θ/cos θ`, whence `θ cos θ ≤ sin θ`, and
`c ≤ θ` with `cos θ ≥ 0` gives `c cos θ ≤ θ cos θ`; for `cos θ = 0` the left
hand side vanishes and `sin θ ≥ 0` on `[0, π]`. -/
theorem mul_cos_le_sin_of_le_fourDiv {c θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hcθ : c ≤ θ) : c * Real.cos θ ≤ Real.sin θ := by
  have hcosnn : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθπ⟩
  by_cases hcos0 : Real.cos θ = 0
  · rw [hcos0, mul_zero]
    exact Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [hθπ, Real.pi_pos]⟩
  · have hcospos : 0 < Real.cos θ := lt_of_le_of_ne' hcosnn hcos0
    have hθlt : θ < Real.pi / 2 :=
      lt_of_le_of_ne hθπ (fun h => hcos0 (by rw [h, Real.cos_pi_div_two]))
    have hmul : θ * Real.cos θ ≤ Real.sin θ := by
      have h := mul_le_mul_of_nonneg_right (Real.le_tan hθ0 hθlt) hcospos.le
      rwa [Real.tan_mul_cos hcos0] at h
    calc c * Real.cos θ ≤ θ * Real.cos θ := mul_le_mul_of_nonneg_right hcθ hcosnn
      _ ≤ Real.sin θ := hmul

/-- `exp (2w) - 1 = 2 exp w sinh w`: the numerator of `ecalPt a u` is a
hyperbolic sine, so the only way it can vanish is `sinh (a u) = 0`. -/
theorem exp_two_mul_sub_one (w : ℂ) :
    Complex.exp (2 * w) - 1 = 2 * Complex.exp w * Complex.sinh w := by
  rw [show (2 : ℂ) * w = w + w by ring, Complex.exp_add, Complex.sinh, Complex.exp_neg]
  field_simp

/-- On the whole transit strip `R/4+2 ≤ Re u ≤ π/λ - R/4` the Écalle point satisfies `‖ecalPt (iλ) u‖ ≤ 4/R`.  Ingredients: with `a = iλ`, `ecalPt a u = λ cos(λu)/sin(λu)`, so `‖ecalPt a u‖² = λ²(cos²(λ Re u) + sinh²(λ Im u))/(sin²(λ Re u) + sinh²(λ Im u))`.  Lower half (`λ·Re u ≤ π/2`): `Direct.ecalPt_norm_le_max` gives `‖ecalPt‖ ≤ max (1/Re u) λ ≤ 4/R`.  Upper half (`λ·Re u ∈ (π/2,π)`): with `b := π/λ - Re u ≥ R/4` one has `cos²(λ Re u) = cos²(λb)`, `sin²(λ Re u) = sin²(λb)`, and `tan t ≥ t` (`Real.lt_tan`) gives `λ cos(λb) ≤ (4/R) sin(λb)`; `λ ≤ 4/R` handles the `sinh²` terms. -/
theorem ecalPt_norm_le_four_div (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (u : ℂ)
    (hx1 : R / 4 + 2 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4) :
    ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R := by
  have hR0 : 0 < R := by linarith
  have hR4 : 0 < R / 4 := by linarith
  have h4R : 0 < 4 / R := div_pos (by norm_num) hR0
  have hlamR4 : 0 < lam * (R / 4) := mul_pos hlam hR4
  -- the basic consequence `lam ≤ 4/R` of `lam R^2 ≤ 1`
  have hlam_le : lam ≤ 4 / R := by
    have h1 : lam ≤ 1 / R ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
      exact hlamR
    have h2 : 1 / R ^ 2 ≤ 4 / R := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
      have he : (4 / R) * R ^ 2 = 4 * R := by field_simp
      rw [he]
      nlinarith
    linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set t : ℝ := lam * u.re with ht
  set s : ℝ := lam * u.im with hs
  have ht_lower : lam * (R / 4) ≤ t := by
    rw [ht]
    exact mul_le_mul_of_nonneg_left (by linarith) hlam.le
  have ht_upper : t ≤ Real.pi - lam * (R / 4) := by
    have h := mul_le_mul_of_nonneg_left hx2 hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * (R / 4) := by
      field_simp
    rw [← ht, he] at h
    exact h
  by_cases hcase : t < Real.pi / 2
  · -- lower half of the strip: reduce to `ecalPt_norm_le_max`
    have hu1 : 0 < u.re := by linarith
    have hu2 : u.re < Real.pi / (2 * lam) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * lam)]
      rw [ht] at hcase
      nlinarith
    refine le_trans (ecalPt_norm_le_max lam hlam u hu1 hu2) (max_le ?_ ?_)
    · have hR4u : R / 4 ≤ u.re := by linarith
      calc 1 / u.re ≤ 1 / (R / 4) := one_div_le_one_div_of_le hR4 hR4u
        _ = 4 / R := by field_simp
    · exact hlam_le
  · -- upper half of the strip
    have hcase' : Real.pi / 2 ≤ t := not_lt.mp hcase
    have htp : 0 < t := by linarith [hcase', Real.pi_pos]
    have htpi : t < Real.pi := by linarith [ht_upper, hlamR4]
    have hsin_pos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htp htpi
    set w : ℂ := a * u with hw
    have hw_im : w.im = t := by
      rw [hw, ha, ht]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
      ring
    have hw_re : w.re = -s := by
      rw [hw, ha, hs]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
      ring
    have hsinh_norm : ‖Complex.sinh w‖ ^ 2 = Real.sin t ^ 2 + Real.sinh s ^ 2 := by
      rw [EcalNorm.norm_sq_sinh, hw_im, hw_re, Real.sinh_neg]
      ring
    -- the denominator of the `coth` formula never vanishes on the upper half
    have hsinh_ne : Complex.sinh w ≠ 0 := by
      intro h0
      have h := hsinh_norm
      rw [h0] at h
      simp at h
      nlinarith [sq_pos_of_pos hsin_pos, sq_nonneg (Real.sinh s)]
    have hEne : Work.Implosion.ecalE a u ≠ 1 := by
      have hid : Work.Implosion.ecalE a u - 1 = 2 * Complex.exp w * Complex.sinh w := by
        have h2w : 2 * a * u = 2 * w := by rw [hw]; ring
        rw [Work.Implosion.ecalE, h2w, exp_two_mul_sub_one]
      intro h1
      have hzero : 2 * Complex.exp w * Complex.sinh w = 0 := by rw [← hid, h1]; ring
      rcases mul_eq_zero.mp hzero with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact (by norm_num : (2 : ℂ) ≠ 0) h4
        · exact Complex.exp_ne_zero w h4
      · exact hsinh_ne h3
    have hden_pos : 0 < Real.sin t ^ 2 + Real.sinh s ^ 2 :=
      by nlinarith [sq_pos_of_pos hsin_pos, sq_nonneg (Real.sinh s)]
    -- the closed form for the squared modulus (`Direct.ecalPt_norm_sq_eq`)
    have hX2 : ‖Work.Implosion.ecalPt a u‖ ^ 2 =
        (lam ^ 2 * (Real.cos t ^ 2 + Real.sinh s ^ 2)) /
          (Real.sin t ^ 2 + Real.sinh s ^ 2) := by
      have h := ecalPt_norm_sq_eq lam hlam u hEne
      rw [← ha, ← ht, ← hs] at h
      rw [h]
      ring
    -- the trigonometric comparison on the upper half
    have hcosθ : Real.cos (Real.pi - t) = -Real.cos t := Real.cos_pi_sub t
    have hsinθ : Real.sin (Real.pi - t) = Real.sin t := Real.sin_pi_sub t
    have hθ0 : 0 ≤ Real.pi - t := by linarith
    have hθhalf : Real.pi - t ≤ Real.pi / 2 := by linarith
    have hkey : lam * (R / 4) * Real.cos (Real.pi - t) ≤ Real.sin (Real.pi - t) :=
      mul_cos_le_sin_of_le_fourDiv hθ0 hθhalf (by linarith [ht_lower])
    have hcosθ_nn : 0 ≤ Real.cos (Real.pi - t) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθhalf⟩
    have hkey' : lam * Real.cos (Real.pi - t) ≤ (4 / R) * Real.sin (Real.pi - t) := by
      have h := mul_le_mul_of_nonneg_left hkey h4R.le
      have he : (4 / R) * (lam * (R / 4) * Real.cos (Real.pi - t))
          = lam * Real.cos (Real.pi - t) := by field_simp
      linarith [h, he]
    have hcos_sq_le : lam ^ 2 * Real.cos t ^ 2 ≤ (4 / R) ^ 2 * Real.sin t ^ 2 := by
      have h := pow_le_pow_left₀ (mul_nonneg hlam.le hcosθ_nn) hkey' 2
      rw [mul_pow, mul_pow, hcosθ, hsinθ, neg_sq] at h
      exact h
    have hsinh_sq_le : lam ^ 2 * Real.sinh s ^ 2 ≤ (4 / R) ^ 2 * Real.sinh s ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlam.le hlam_le 2) (sq_nonneg _)
    have htarget : lam ^ 2 * (Real.cos t ^ 2 + Real.sinh s ^ 2)
        ≤ (4 / R) ^ 2 * (Real.sin t ^ 2 + Real.sinh s ^ 2) := by
      nlinarith [hcos_sq_le, hsinh_sq_le]
    have hsqgoal : ‖Work.Implosion.ecalPt a u‖ ^ 2 ≤ (4 / R) ^ 2 := by
      rw [hX2, div_le_iff₀ hden_pos]
      exact htarget
    have hle := sq_le_sq.mp hsqgoal
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h4R.le] at hle

end Work.PARIMPL2.Direct
