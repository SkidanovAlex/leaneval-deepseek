import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric

namespace Commons.Analysis.SpecialFunctions.Trigonometric

open Complex
open scoped ComplexConjugate

/-- For a complex number `w` with `‖w‖ < 1`, the quotient `(1 - w) / (1 + w)` is bounded by
`(1 + ‖w‖) * (1 - ‖w‖)⁻¹`. -/
lemma norm_one_sub_div_one_add_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 - w) / (1 + w)‖ ≤ (1 + ‖w‖) * (1 - ‖w‖)⁻¹ := by
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hnum : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    calc
      ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le (1 : ℂ) w
      _ = 1 + ‖w‖ := by simp
  have htri : ‖(1 : ℂ) + w - w‖ ≤ ‖1 + w‖ + ‖w‖ := norm_sub_le (1 + w) w
  have hsum : ‖(1 : ℂ) + w - w‖ = 1 := by
    have : (1 : ℂ) + w - w = 1 := by ring
    rw [this, norm_one]
  have hmain : 1 - ‖w‖ ≤ ‖1 + w‖ := by linarith
  have h1wpos : 0 < ‖1 + w‖ := lt_of_lt_of_le hpos hmain
  have hinv : ‖(1 + w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ h1wpos hpos).2 hmain
  calc
    ‖(1 - w) / (1 + w)‖ = ‖(1 - w) * (1 + w)⁻¹‖ := by rw [div_eq_mul_inv]
    _ = ‖1 - w‖ * ‖(1 + w)⁻¹‖ := by rw [Complex.norm_mul]
    _ ≤ (1 + ‖w‖) * (1 - ‖w‖)⁻¹ := by
      exact mul_le_mul hnum hinv (norm_nonneg _) (by positivity)

/-- The elementary bound `e⁻² ≤ 1/3`. -/
lemma exp_neg_two_le_third : Real.exp (-2) ≤ (1 / 3 : ℝ) := by
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    norm_num at h ⊢
    exact h
  have hpos3 : (0 : ℝ) < 3 := by norm_num
  have hposexp : 0 < Real.exp 2 := Real.exp_pos 2
  have hinv : (Real.exp 2)⁻¹ ≤ (3 : ℝ)⁻¹ := (inv_le_inv₀ hposexp hpos3).2 hexp2
  rw [Real.exp_neg]
  simpa using hinv

/-- Euler-style formula for the complex tangent:
`tan z = I * (1 - exp (2 * z * I)) / (1 + exp (2 * z * I))`
whenever the displayed denominators are non-zero. -/
lemma tan_eq_I_one_sub_exp_div (z : ℂ) (hcos : cos z ≠ 0)
    (hden : 1 + exp (2 * z * I) ≠ 0) :
    Complex.tan z = I * (1 - exp (2 * z * I)) / (1 + exp (2 * z * I)) := by
  have hmul : sin z * (1 + exp (2 * z * I)) = I * (1 - exp (2 * z * I)) * cos z := by
    let u : ℂ := exp (z * I)
    have hu : u ≠ 0 := by
      dsimp [u]
      exact Complex.exp_ne_zero _
    have hw : exp (2 * z * I) = u ^ 2 := by
      dsimp [u]
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    have hneg : exp (-z * I) = u⁻¹ := by
      dsimp [u]
      rw [← Complex.exp_neg]
      congr 1
      ring
    simp only [Complex.sin, Complex.cos]
    rw [hw, hneg]
    field_simp [hu]
    ring
  rw [Complex.tan_eq_sin_div_cos]
  calc
    sin z / cos z = (sin z * (1 + exp (2 * z * I))) / (cos z * (1 + exp (2 * z * I))) := by
      field_simp [hcos, hden]
    _ = (I * (1 - exp (2 * z * I)) * cos z) / (cos z * (1 + exp (2 * z * I))) := by
      rw [hmul]
    _ = I * (1 - exp (2 * z * I)) / (1 + exp (2 * z * I)) := by
      field_simp [hcos]

/-- For `z` with imaginary part at least one, `‖tan z‖ ≤ 2`. -/
lemma norm_tan_le_two_of_one_le_im (z : ℂ) (hz : (1 : ℝ) ≤ z.im) :
    ‖Complex.tan z‖ ≤ 2 := by
  by_cases hcos : cos z = 0
  · rw [Complex.tan_eq_sin_div_cos, hcos]
    simp
  · have hw_le : ‖exp (2 * z * I)‖ ≤ (1 / 3 : ℝ) := by
      calc
        ‖exp (2 * z * I)‖ = Real.exp (-2 * z.im) := by
          rw [Complex.norm_exp]
          congr 1
          simp [Complex.mul_re, Complex.mul_im]
        _ ≤ Real.exp (-2) := Real.exp_le_exp_of_le (by nlinarith [hz])
        _ ≤ (1 / 3 : ℝ) := exp_neg_two_le_third
    have hden : 1 + exp (2 * z * I) ≠ 0 := by
      intro h
      have hwneg : exp (2 * z * I) = -1 := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)
      have : ‖exp (2 * z * I)‖ = 1 := by
        rw [hwneg, norm_neg, norm_one]
      linarith
    have htan := tan_eq_I_one_sub_exp_div z hcos hden
    have hwlt : ‖exp (2 * z * I)‖ < 1 := lt_of_le_of_lt hw_le (by norm_num)
    have hb : ‖(1 - exp (2 * z * I)) / (1 + exp (2 * z * I))‖ ≤
        (1 + ‖exp (2 * z * I)‖) * (1 - ‖exp (2 * z * I)‖)⁻¹ :=
      norm_one_sub_div_one_add_le hwlt
    have hnormeq : ‖Complex.tan z‖ = ‖(1 - exp (2 * z * I)) / (1 + exp (2 * z * I))‖ := by
      rw [htan]
      simp
    rw [hnormeq]
    have hpos : 0 < 1 - ‖exp (2 * z * I)‖ := by linarith [norm_nonneg (exp (2 * z * I))]
    have hfinal : (1 + ‖exp (2 * z * I)‖) * (1 - ‖exp (2 * z * I)‖)⁻¹ ≤ 2 := by
      have hlm : 1 + ‖exp (2 * z * I)‖ ≤ 2 * (1 - ‖exp (2 * z * I)‖) := by
        nlinarith [hw_le]
      calc
        (1 + ‖exp (2 * z * I)‖) * (1 - ‖exp (2 * z * I)‖)⁻¹
            ≤ (2 * (1 - ‖exp (2 * z * I)‖)) * (1 - ‖exp (2 * z * I)‖)⁻¹ := by
              exact mul_le_mul_of_nonneg_right hlm (inv_nonneg.mpr hpos.le)
        _ = 2 := by field_simp [hpos.ne']
    exact le_trans hb hfinal

/-- For any complex number whose imaginary part is at least one in absolute value, the tangent is
bounded by four in norm. -/
theorem tan_norm_le_of_abs_im_ge (z : ℂ) (hz : (1 : ℝ) ≤ |z.im|) :
    ‖Complex.tan z‖ ≤ 4 := by
  rcases le_abs.mp hz with h1 | h2
  · have hb := norm_tan_le_two_of_one_le_im z h1
    linarith
  · have hb : ‖Complex.tan z‖ ≤ 2 := by
      have hb' := norm_tan_le_two_of_one_le_im (-z) (by simpa [Complex.neg_im] using h2)
      simpa [Complex.tan_neg] using hb'
    linarith

end Commons.Analysis.SpecialFunctions.Trigonometric