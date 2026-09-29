import Mathlib
import Submission.Work.CNum.C2_setup

namespace Work.CNum

open Complex

/-- A complex number with positive real part is the principal square root of its square. -/
lemma sqrt_sq_eq_of_re_pos {v : ℂ} (hv : 0 < v.re) : Complex.sqrt (v ^ 2) = v := by
  rw [Complex.sqrt]
  exact Complex.sq_cpow_two_inv hv

/-- On the arc `θ ∈ (α, 2π-α)`, `R(e^{iθ}) = 2A(γ - cos θ)·(-e^{iθ})` and the principal square
root has positive real part, giving `√R(e^{iθ}) = -i·√(2A(γ-cos θ))·e^{iθ/2}`. -/
theorem C2_sqrt_Ra {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Complex.sqrt (Ra (Complex.exp (Complex.I * θ))) =
      -(Complex.I * (C2T θ : ℂ)) * Complex.exp (Complex.I * (θ / 2)) := by
  set m : ℝ := 2 * AR * (gamR - Real.cos θ) with hm_def
  have hAR : 0 < AR := by simp only [AR, cR]; norm_num
  -- `cos θ < γ` on the arc
  have hcos : Real.cos θ < gamR := by
    have hpc : Real.pi - alpR ≤ Real.pi := by linarith [alpR_nonneg]
    have habs : |Real.pi - θ| < Real.pi - alpR := by
      rw [abs_lt]; constructor <;> linarith [h.1, h.2]
    have hclt : -gamR < Real.cos |Real.pi - θ| := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi - θ)) hpc habs
      rwa [Real.cos_pi_sub, cos_alpR] at this
    have hcos' : Real.cos θ = -Real.cos |Real.pi - θ| := by
      rw [Real.cos_abs, Real.cos_pi_sub]; ring
    linarith
  have hm : 0 < m := by
    rw [hm_def]
    have h2 : 0 < 2 * AR := by linarith
    have h3 : 0 < gamR - Real.cos θ := by linarith
    exact mul_pos h2 h3
  have hBR : BR = 2 * AR * (1 + gamR) := by simp only [BR, AR, gamR, cR]; norm_num
  -- the algebraic identity `R(e^{iθ}) = m·(-e^{iθ})`
  have hz : Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      (m : ℂ) * (- Complex.exp (Complex.I * (θ : ℂ))) := by
    set u : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hu
    have hu0 : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
    have h1 : (1 + u) ^ 2 = u * (2 + u + u⁻¹) := by field_simp; ring
    have h2 : u + u⁻¹ = (2 * Real.cos θ : ℂ) := by
      rw [hu]
      rw [show (Complex.exp (Complex.I * (θ : ℂ)))⁻¹ = Complex.exp (-(Complex.I * (θ : ℂ)))
            from (Complex.exp_neg _).symm]
      rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I from mul_comm _ _]
      rw [show -(↑θ * Complex.I) = -(↑θ) * Complex.I from by ring]
      rw [← Complex.two_cos, Complex.ofReal_cos]
    have h3 : (AR : ℂ) * (2 + u + u⁻¹) - (BR : ℂ) = -(m : ℂ) := by
      rw [show (2 + u + u⁻¹ : ℂ) = 2 + (u + u⁻¹) by ring, h2]
      rw [show (BR : ℂ) = 2 * (AR : ℂ) * (1 + (gamR : ℂ)) by rw [hBR]; push_cast; ring]
      rw [hm_def]; push_cast; ring
    calc Ra u = (AR : ℂ) * (1 + u) ^ 2 - (BR : ℂ) * u := rfl
      _ = (AR : ℂ) * (u * (2 + u + u⁻¹)) - (BR : ℂ) * u := by rw [h1]
      _ = u * ((AR : ℂ) * (2 + u + u⁻¹) - (BR : ℂ)) := by ring
      _ = u * (-(m : ℂ)) := by rw [h3]
      _ = (m : ℂ) * (-u) := by ring
  -- `(C2T θ)² = m`
  have hsqC2T : (C2T θ) ^ 2 = m := by
    rw [hm_def, C2T]
    exact Real.sq_sqrt hm.le
  have hC2Tpos : 0 < C2T θ := by rw [C2T]; exact Real.sqrt_pos_of_pos hm
  have hsin : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [alpR_pos, h.1]
    · linarith [h.2, alpR_pos]
  -- square of the claimed root
  have hI : (-(Complex.I * (C2T θ : ℂ))) ^ 2 = -(m : ℂ) := by
    have hs : (C2T θ : ℂ) ^ 2 = (m : ℂ) := by rw [← Complex.ofReal_pow, hsqC2T]
    calc (-(Complex.I * (C2T θ : ℂ))) ^ 2 = (Complex.I * (C2T θ : ℂ)) ^ 2 := by ring
      _ = Complex.I ^ 2 * (C2T θ : ℂ) ^ 2 := by ring
      _ = -(m : ℂ) := by rw [Complex.I_sq, hs]; ring
  have he2 : Complex.exp (Complex.I * ((θ : ℂ) / 2)) ^ 2 =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hw2 : (-(Complex.I * (C2T θ : ℂ)) * Complex.exp (Complex.I * (θ / 2))) ^ 2 =
      Ra (Complex.exp (Complex.I * (θ : ℂ))) := by
    rw [mul_pow, hI, he2, hz]
    ring
  -- positive real part of the claimed root
  have hwre : 0 < (-(Complex.I * (C2T θ : ℂ)) * Complex.exp (Complex.I * (θ / 2))).re := by
    rw [Complex.mul_re]
    have h1 : (-(Complex.I * (C2T θ : ℂ))).re = 0 := by
      simp [Complex.neg_re, Complex.ofReal_im]
    have h2 : (-(Complex.I * (C2T θ : ℂ))).im = -(C2T θ) := by
      simp [Complex.neg_im, Complex.ofReal_re]
    have h3 : (Complex.exp (Complex.I * (θ / 2))).im = Real.sin (θ / 2) := by
      have harg : Complex.I * (θ / 2) = ((θ / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg]
      exact Complex.exp_ofReal_mul_I_im (θ / 2)
    rw [h1, h2, h3]
    nlinarith [hC2Tpos, hsin]
  rw [← hw2]
  exact sqrt_sq_eq_of_re_pos hwre

end Work.CNum
