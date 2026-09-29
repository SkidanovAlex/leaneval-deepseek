import Mathlib
import Submission.Work.CNum.Basic

/-! # `Work.CNum.C2_mem`

For `θ` in the cusp arc `(α, 2π - α)`, the normalised point
`V(θ) = ((3/4)·ψ_C(e^{iθ}) - c₂)/ρ₂` lies on the unit circle: `‖Vof θ‖ = 1`.

The proof is a direct computation.  Writing `z = e^{iθ}`, `s = c²-1`, `t = 1+c²` and
`σ = √(Ra z)` one has

* `Vof θ = -(t(1+z) + σ)/(4c)`,
* on the arc `Ra z = 2A(cos θ - γ)·z` with `cos θ - γ < 0`, so `σ = -i·P̃·e^{iθ/2}`
  where `P̃ = √(2A(γ - cos θ)) ≥ 0`,
* hence `t(1+z) + σ = e^{iθ/2}·(2t cos(θ/2) - iP̃)` and
  `‖2t cos(θ/2) - iP̃‖² = 4t²cos²(θ/2) + P̃² = 2A(1+cos θ) + 2A(γ - cos θ) = 2A(1+γ) = 16c²`.
-/

namespace Work.CNum

open Complex

/-! ### Principal square roots -/

/-- If `Re x > 0` then `x` is the principal square root of `x²`. -/
private lemma sqrt_sq_of_re_pos {x : ℂ} (hx : 0 < x.re) : Complex.sqrt (x ^ 2) = x := by
  have hn : ‖x ^ 2‖ = x.re ^ 2 + x.im ^ 2 := by
    rw [pow_two, norm_mul, ← pow_two, Complex.sq_norm, Complex.normSq_apply]; ring
  have hre2 : (x ^ 2).re = x.re ^ 2 - x.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have him2 : (x ^ 2).im = 2 * x.re * x.im := by
    rw [pow_two, Complex.mul_im]; ring
  apply Complex.ext
  · rw [Complex.sqrt, Complex.cpow_inv_two_re, hre2, hn]
    rw [show (x.re ^ 2 + x.im ^ 2 + (x.re ^ 2 - x.im ^ 2)) / 2 = x.re ^ 2 by ring]
    exact Real.sqrt_sq (le_of_lt hx)
  · rw [Complex.sqrt]
    by_cases h : 0 ≤ (x ^ 2).im
    · rw [Complex.cpow_inv_two_im_eq_sqrt h, hre2, hn]
      rw [show (x.re ^ 2 + x.im ^ 2 - (x.re ^ 2 - x.im ^ 2)) / 2 = x.im ^ 2 by ring]
      have hxi : 0 ≤ x.im := by rw [him2] at h; nlinarith [hx]
      exact Real.sqrt_sq hxi
    · rw [Complex.cpow_inv_two_im_eq_neg_sqrt (lt_of_not_ge h), hre2, hn]
      rw [show (x.re ^ 2 + x.im ^ 2 - (x.re ^ 2 - x.im ^ 2)) / 2 = (-x.im) ^ 2 by ring]
      have hxi : x.im < 0 := by rw [him2] at h; nlinarith [hx]
      rw [Real.sqrt_sq (by linarith)]
      ring

/-! ### Elementary exponential identities -/

private lemma exp_I_half_sq (θ : ℝ) : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) ^ 2 =
    Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private lemma one_add_exp (θ : ℝ) :
    1 + Complex.exp (Complex.I * (θ : ℂ)) =
      2 * (Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I]
  have h2 : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [mul_comm Complex.I (((θ / 2 : ℝ)) : ℂ), Complex.exp_ofReal_mul_I]
  rw [h1, h2]
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; linarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; linarith
  rw [hc, hs]; push_cast; ring

/-! ### The radicand on the unit circle -/

/-- `Ra (e^{iθ}) = 2A(cos θ - γ)·e^{iθ}` for every `θ`. -/
lemma Ra_exp (θ : ℝ) : Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
  have hBR : BR = 2 * AR * (1 + gamR) := by simp only [BR, AR, gamR, cR]; norm_num
  set u : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hu
  have hu0 : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
  have h1 : (1 + u) ^ 2 = u * (2 + u + u⁻¹) := by field_simp; ring
  have h2 : u + u⁻¹ = (2 * Real.cos θ : ℂ) := by
    rw [hu]
    rw [show (Complex.exp (Complex.I * (θ : ℂ)))⁻¹ = Complex.exp (-(Complex.I * (θ : ℂ)))
          from (Complex.exp_neg _).symm]
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I from mul_comm _ _]
    rw [show -(↑θ * Complex.I) = -(↑θ) * Complex.I from by ring]
    rw [← Complex.two_cos]
    rw [Complex.ofReal_cos]
  have h3 : (AR : ℂ) * (2 + u + u⁻¹) - (BR : ℂ) =
      ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) := by
    rw [show (2 + u + u⁻¹ : ℂ) = 2 + (u + u⁻¹) by ring, h2]
    rw [show (BR : ℂ) = 2 * (AR : ℂ) * (1 + (gamR : ℂ)) by rw [hBR]; push_cast; ring]
    push_cast
    ring
  calc Ra u = (AR : ℂ) * (1 + u) ^ 2 - (BR : ℂ) * u := rfl
    _ = (AR : ℂ) * (u * (2 + u + u⁻¹)) - (BR : ℂ) * u := by rw [h1]
    _ = u * ((AR : ℂ) * (2 + u + u⁻¹) - (BR : ℂ)) := by ring
    _ = u * ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) := by rw [h3]
    _ = ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) * u := by ring

/-! ### The cusp arc -/

/-- On the arc `(α, 2π - α)` the cosine is strictly below `γ = cos α`. -/
lemma cos_lt_gamR {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Real.cos θ < gamR := by
  have hgm1 : -1 < gamR := by simp only [gamR, AR, cR]; norm_num
  have hgm2 : gamR < 1 := by simp only [gamR, AR, cR]; norm_num
  have ha0 : 0 < alpR := Real.arccos_pos.mpr hgm2
  have haPi : alpR < Real.pi := Real.arccos_lt_pi.mpr hgm1
  have hcosalp : Real.cos alpR = gamR := Real.cos_arccos hgm1.le hgm2.le
  rw [← hcosalp]
  have h1 : 0 < Real.sin ((θ + alpR) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1, ha0]) (by linarith [h.2, haPi])
  have h2 : 0 < Real.sin ((θ - alpR) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, haPi])
  have hkey := Real.cos_sub_cos θ alpR
  nlinarith [h1, h2, hkey]

private lemma two_AR_one_add_gamR : 2 * AR * (1 + gamR) = 16 * cR ^ 2 := by
  simp only [gamR, AR, cR]; norm_num

/-! ### The main computation -/

/-- `‖t(1 + e^{iθ}) + √(Ra (e^{iθ}))‖ = 4c` on the arc `(α, 2π - α)`. -/
private lemma norm_key {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    ‖(((1 + cR ^ 2 : ℝ)) : ℂ) * (1 + Complex.exp (Complex.I * (θ : ℂ))) +
      Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ))))‖ = 4 * cR := by
  have hgm1 : -1 < gamR := by simp only [gamR, AR, cR]; norm_num
  have hgm2 : gamR < 1 := by simp only [gamR, AR, cR]; norm_num
  have ha0 : 0 < alpR := Real.arccos_pos.mpr hgm2
  have haPi : alpR < Real.pi := Real.arccos_lt_pi.mpr hgm1
  have hcR : (0 : ℝ) < cR := by simp only [cR]; norm_num
  set z : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hz
  set e : ℂ := Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) with he
  have he2 : e ^ 2 = z := by rw [he, hz]; exact exp_I_half_sq θ
  set pp : ℝ := Real.sqrt (2 * AR * (gamR - Real.cos θ)) with hpp
  have hARpos : 0 < AR := by rw [AR]; positivity
  have hpp_pos : 0 < pp := by
    rw [hpp]; apply Real.sqrt_pos_of_pos; nlinarith [cos_lt_gamR h]
  have hpp_sq : pp ^ 2 = 2 * AR * (gamR - Real.cos θ) := by
    rw [hpp]; exact Real.sq_sqrt (by nlinarith [cos_lt_gamR h])
  set w : ℂ := (-Complex.I * (pp : ℂ)) * e with hw
  set A0 : ℂ := ((1 + cR ^ 2 : ℝ) : ℂ) * ((2 * Real.cos (θ / 2) : ℝ) : ℂ) -
    Complex.I * (pp : ℂ) with hA0def
  have hRa_z : Ra z = ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) * z := by
    rw [hz]; exact Ra_exp θ
  have hw_sq : w ^ 2 = Ra z := by
    rw [hw, hRa_z]
    rw [show ((-Complex.I * (pp : ℂ)) * e) ^ 2 = (-Complex.I) ^ 2 * (pp : ℂ) ^ 2 * e ^ 2 by ring]
    rw [he2]
    rw [show (-Complex.I) ^ 2 = (-1 : ℂ) by rw [neg_sq, pow_two, Complex.I_mul_I]]
    rw [show (pp : ℂ) ^ 2 = ((2 * AR * (gamR - Real.cos θ) : ℝ) : ℂ) by
        rw [← Complex.ofReal_pow, hpp_sq]]
    push_cast
    ring
  have hwre_eq : w.re = pp * e.im := by
    rw [hw, Complex.mul_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hw_re : 0 < w.re := by
    rw [hwre_eq]
    have he_im : e.im = Real.sin (θ / 2) := by
      rw [he, show Complex.I * ((θ / 2 : ℝ) : ℂ) = (((θ / 2 : ℝ)) : ℂ) * Complex.I from
        mul_comm _ _]
      exact Complex.exp_ofReal_mul_I_im (θ / 2)
    rw [he_im]
    have hsin : 0 < Real.sin (θ / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [h.1, ha0]
      · linarith [h.2, haPi]
    nlinarith [hpp_pos, hsin]
  have hsqrt : Complex.sqrt (Ra z) = w := by
    rw [← hw_sq]; exact sqrt_sq_of_re_pos hw_re
  rw [hsqrt]
  have h1z : (1 : ℂ) + z = (2 * (Real.cos (θ / 2) : ℂ)) * e := by
    rw [hz, he]; exact one_add_exp θ
  have hnumeq : ((1 + cR ^ 2 : ℝ) : ℂ) * (1 + z) + w = A0 * e := by
    rw [h1z, hw, hA0def]; push_cast; ring
  rw [hnumeq, norm_mul]
  have henorm : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]; simp [Complex.mul_re]
  rw [henorm, mul_one]
  have hA0 : ‖A0‖ = 4 * cR := by
    have hre : A0.re = 2 * (1 + cR ^ 2) * Real.cos (θ / 2) := by
      rw [hA0def]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero]
      ring
    have him : A0.im = -pp := by
      rw [hA0def]
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, add_zero]
      ring
    have hns : Complex.normSq A0 = 16 * cR ^ 2 := by
      have hARval : AR = (1 + cR ^ 2) ^ 2 := rfl
      rw [Complex.normSq_apply, hre, him]
      have hc2 : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
        have h1 := Real.cos_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at h1
        have h2 := Real.sin_sq (θ / 2); nlinarith
      nlinarith [hc2, two_AR_one_add_gamR, hARval, hpp_sq]
    have h1 : ‖A0‖ ^ 2 = (4 * cR) ^ 2 := by rw [Complex.sq_norm, hns]; ring
    exact (sq_eq_sq₀ (norm_nonneg A0) (by linarith [hcR])).mp h1
  rw [hA0]

/-- The reduction of `Vof` to the explicit expression `-(t(1+z)+√(Ra z))/(4c)`. -/
private lemma Vof_eq (θ : ℝ) : Vof θ = -(((1 + cR ^ 2 : ℝ) : ℂ) *
    (1 + Complex.exp (Complex.I * (θ : ℂ))) +
    Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ))))) / (4 * cR) := by
  rw [Vof, Wfun, cenC2, dR, rho2sq, aR, bR, c0R, kR, cR]
  norm_num
  ring

theorem C2_mem {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) : ‖Vof θ‖ = 1 := by
  have hcR : (0 : ℝ) < cR := by simp only [cR]; norm_num
  set z : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hz
  have hkey : ‖((1 + cR ^ 2 : ℝ) : ℂ) * (1 + z) + Complex.sqrt (Ra z)‖ = 4 * cR := by
    rw [hz]; exact norm_key h
  have hV : Vof θ = -(((1 + cR ^ 2 : ℝ) : ℂ) * (1 + z) + Complex.sqrt (Ra z)) / (4 * cR) := by
    rw [hz]; exact Vof_eq θ
  rw [hV, norm_div, norm_neg, hkey]
  have h4 : ‖((4 : ℂ) * (cR : ℂ))‖ = 4 * cR := by
    rw [norm_mul]
    rw [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcR]
  rw [h4]
  exact div_self (by linarith [hcR])

end Work.CNum
