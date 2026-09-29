import Mathlib
import Submission.Work.CNum.Basic

namespace Work.CNum

/-- On the arc `θ ∈ (-α, α)` the radicand `R(e^{iθ})` equals `e^{iθ}·2·A·(cos θ - γ)`, i.e.
`√R(e^{iθ}) = P(θ)·e^{iθ/2}` for the principal square root. -/
theorem sqrt_Ra_circle {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ)))) =
      (PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
  have hgm1 : -1 < gamR := by simp only [gamR, AR, cR]; norm_num
  have hgm2 : gamR < 1 := by simp only [gamR, AR, cR]; norm_num
  have hAR : 0 < AR := by simp only [AR, cR]; norm_num
  have ha : alpR < Real.pi := by rw [alpR, Real.arccos_lt_pi]; exact hgm1
  -- `cos θ > γ` on the arc
  have hcos : gamR < Real.cos θ := by
    have h1 : Real.cos alpR < Real.cos |θ| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) (le_of_lt ha) (abs_lt.mpr ⟨h.1, h.2⟩)
    rw [Real.cos_abs, alpR, Real.cos_arccos hgm1.le hgm2.le] at h1
    exact h1
  -- `P(θ)² = 2A(cos θ - γ)`
  have hPRsq : PR θ ^ 2 = 2 * AR * (Real.cos θ - gamR) := by
    rw [PR, Real.sq_sqrt (by nlinarith)]
  -- the constant relation `B = 2A(1+γ)`
  have hBR : BR = 2 * AR * (1 + gamR) := by simp only [BR, AR, gamR, cR]; norm_num
  -- algebraic identity: `R(e^{iθ}) = 2A(cos θ - γ)·e^{iθ}`
  have hz : Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
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
  set w : ℂ := (PR θ : ℂ) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) with hw
  -- `e^{iθ/2}² = e^{iθ}`
  have he2 : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) ^ 2 =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- `w² = R(e^{iθ})`
  have hsq : Ra (Complex.exp (Complex.I * (θ : ℂ))) = w ^ 2 := by
    rw [hw, mul_pow, he2]
    rw [show (PR θ : ℂ) ^ 2 = ((2 * AR * (Real.cos θ - gamR) : ℝ) : ℂ) from by
      rw [← Complex.ofReal_pow, hPRsq]]
    exact hz
  -- `Re w > 0`, so `w` is the principal square root of `w²`
  have hwre : 0 < w.re := by
    rw [hw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hc : (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))).re = Real.cos (θ / 2) := by
      rw [show Complex.I * ((θ / 2 : ℝ) : ℂ) = (((θ / 2 : ℝ)) : ℂ) * Complex.I from mul_comm _ _]
      exact Complex.exp_ofReal_mul_I_re (θ / 2)
    rw [hc]
    have hcos2 : 0 < Real.cos (θ / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [h.1, h.2, le_of_lt ha]
    have hPRpos : 0 < PR θ := by rw [PR]; apply Real.sqrt_pos_of_pos; nlinarith
    positivity
  rw [hsq]
  show Complex.sqrt (w ^ 2) = w
  rw [Complex.sqrt]
  exact Complex.sq_cpow_two_inv hwre

end Work.CNum
