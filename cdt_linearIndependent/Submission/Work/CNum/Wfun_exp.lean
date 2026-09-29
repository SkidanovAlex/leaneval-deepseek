import Mathlib
import Submission.Work.CNum.Basic

/-! # `Work.CNum.Wfun_exp`

Evaluation of the inverse-branch map `Wfun` on the unit circle at `z = e^{iθ}`, for
`θ` in the cusp arc `(-α, α)`.  Writing `w = e^{iθ/2}` and
`P = PR θ = √(2A(cos θ - γ))`, `Q = QR θ = 2(1+c²) sin(θ/2)`, we show

  `Wfun (e^{iθ}) = -((P + iQ) w) / d`.

The proof is a direct computation:
* `1 + e^{iθ} = 2 cos(θ/2) w`  and  `e^{iθ} - 1 = 2 i sin(θ/2) w`;
* `Ra (e^{iθ}) = (P w)²`  (using `A(1+z)² - Bz` and the algebraic relation
  `2 A γ = B - 2 A`);
* `Re (P w) > 0`, so the principal square root `√(Ra (e^{iθ})) = P w`.
-/

namespace Work.CNum

/-! ### Elementary trigonometric identities -/

private lemma cos_add_one (θ : ℝ) : (1 + Real.cos θ) = 2 * Real.cos (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

private lemma cos_sub_one' (θ : ℝ) : Real.cos θ - 1 = -2 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  have h2 := Real.sin_sq (θ / 2)
  linarith

private lemma sin_eq' (θ : ℝ) : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
  have h := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-! ### The two half-angle exponential identities -/

private lemma exp_I_eq (θ : ℝ) : Complex.exp (Complex.I * (θ : ℂ)) =
    (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I]

private lemma one_add_exp (θ : ℝ) :
    1 + Complex.exp (Complex.I * (θ : ℂ)) =
      2 * (Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
  rw [exp_I_eq θ, exp_I_eq (θ / 2)]
  rw [show (2 : ℂ) * (Real.cos (θ / 2) : ℂ) *
        ((Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I)
      = (2 * Real.cos (θ / 2) * Real.cos (θ / 2) : ℂ) +
        (2 * Real.cos (θ / 2) * Real.sin (θ / 2) : ℂ) * Complex.I by ring]
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by linarith [cos_add_one θ]
  rw [hc, sin_eq' θ]
  push_cast
  ring

private lemma exp_sub_one (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - 1 =
      (2 * Complex.I * (Real.sin (θ / 2) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
  rw [exp_I_eq θ, exp_I_eq (θ / 2)]
  rw [show (2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ) *
        ((Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I)
      = (2 * Real.sin (θ / 2) * Real.sin (θ / 2) : ℂ) * (Complex.I * Complex.I) +
        (2 * Real.sin (θ / 2) * Real.cos (θ / 2) : ℂ) * Complex.I by ring]
  rw [Complex.I_mul_I]
  have hc : Real.cos θ = -2 * Real.sin (θ / 2) ^ 2 + 1 := by linarith [cos_sub_one' θ]
  rw [hc, sin_eq' θ]
  push_cast
  ring

private lemma exp_I_half_sq (θ : ℝ) : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) ^ 2 =
    Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

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

/-! ### Basic facts about the constants -/

private lemma gamR_bounds : -1 < gamR ∧ gamR < 1 := by
  constructor <;> (rw [gamR, AR, cR]; norm_num)

private lemma gamR_rel : 2 * AR * gamR = BR - 2 * AR := by
  have hAR : AR ≠ 0 := by rw [AR]; positivity
  rw [gamR, BR]; field_simp; ring

/-! ### Positivity on the arc -/

private lemma cos_theta_gt_gamR {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    gamR < Real.cos θ := by
  have hgam := gamR_bounds
  have hcos : Real.cos alpR = gamR := Real.cos_arccos hgam.1.le hgam.2.le
  have halp_lt_pi : alpR < Real.pi := Real.arccos_lt_pi.mpr hgam.1
  have hθabs : |θ| < alpR := abs_lt.mpr ⟨h.1, h.2⟩
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) halp_lt_pi.le hθabs
  rwa [hcos, Real.cos_abs] at this

private lemma twoAR_pos {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    0 < 2 * AR * (Real.cos θ - gamR) := by
  have h1 := cos_theta_gt_gamR h
  have h2 : 0 < AR := by rw [AR]; positivity
  nlinarith [h1]

private lemma PR_sq {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    PR θ ^ 2 = 2 * AR * (Real.cos θ - gamR) := by
  rw [PR]; exact Real.sq_sqrt (le_of_lt (twoAR_pos h))

private lemma PR_pos {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) : 0 < PR θ := by
  rw [PR]; exact Real.sqrt_pos_of_pos (twoAR_pos h)

private lemma cos_half_pos {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    0 < Real.cos (θ / 2) := by
  have hgam := gamR_bounds
  have halp_lt_pi : alpR < Real.pi := Real.arccos_lt_pi.mpr hgam.1
  have hθabs : |θ| < alpR := abs_lt.mpr ⟨h.1, h.2⟩
  have hθpi : |θ| < Real.pi := lt_trans hθabs halp_lt_pi
  have h' : -(Real.pi) < θ ∧ θ < Real.pi := abs_lt.mp hθpi
  exact Real.cos_pos_of_mem_Ioo (by rw [Set.mem_Ioo]; constructor <;> linarith)

/-! ### The radicand on the circle -/

private lemma sqrt_Ra_exp {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ)))) =
      (PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
  have hkey : 4 * AR * Real.cos (θ / 2) ^ 2 - BR = 2 * AR * (Real.cos θ - gamR) := by
    have e1 : 4 * AR * Real.cos (θ / 2) ^ 2 = 2 * AR * (1 + Real.cos θ) := by
      have hcc : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by linarith [cos_add_one θ]
      rw [hcc]; ring
    have hge : BR = 2 * AR * gamR + 2 * AR := by linarith [gamR_rel]
    rw [e1, hge]; ring
  have hL : Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2 := by
    rw [Ra, one_add_exp θ, ← exp_I_half_sq θ]
    rw [show (2 * (Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * ↑(θ / 2))) ^ 2
        = ((4 * Real.cos (θ / 2) ^ 2 : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ↑(θ / 2))) ^ 2 by push_cast; ring]
    rw [show (AR : ℂ) * (((4 * Real.cos (θ / 2) ^ 2 : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ↑(θ / 2))) ^ 2) -
          (BR : ℂ) * (Complex.exp (Complex.I * ↑(θ / 2))) ^ 2
        = ((4 * AR * Real.cos (θ / 2) ^ 2 - BR : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ↑(θ / 2))) ^ 2 by push_cast; ring]
    rw [hkey]
  have hR : ((PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2 =
      ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2 := by
    rw [show ((PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2
        = ((PR θ : ℂ) ^ 2) * (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2 by ring]
    rw [show (PR θ : ℂ) ^ 2 = ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) by
          rw [← Complex.ofReal_pow, PR_sq h]]
  have hsq : Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      ((PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) ^ 2 := hL.trans hR.symm
  have hre : 0 < ((PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))).re := by
    rw [exp_I_eq (θ / 2), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
    have h1 := PR_pos h
    have h2 := cos_half_pos h
    nlinarith [h1, h2]
  rw [hsq, sqrt_sq_of_re_pos hre]

/-! ### The main theorem -/

theorem Wfun_exp {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Wfun (Complex.exp (Complex.I * (θ : ℂ))) =
      -((((PR θ : ℝ) : ℂ) + Complex.I * (QR θ : ℂ)) *
          Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) / (dR : ℂ) := by
  have hsub := exp_sub_one θ
  have hsqrt := sqrt_Ra_exp h
  have hnum : (1 + (cR : ℂ) ^ 2) * (Complex.exp (Complex.I * (θ : ℂ)) - 1) +
      Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ))))
      = ((PR θ : ℂ) + Complex.I * (QR θ : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
    rw [hsub, hsqrt, QR]; push_cast; ring
  rw [Wfun, hnum]
  simp only [neg_div]

end Work.CNum
