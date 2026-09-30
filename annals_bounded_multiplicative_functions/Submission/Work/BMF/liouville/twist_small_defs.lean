import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial Finset Real

noncomputable section

/-- The weight `H(s) = (1 + 1/s)/s` appearing in the integrand
`t^{-1-iu} * (1 + 1/log t)/log t = t^{-1-iu} * H(log t)`. -/
def Hw (s : ℝ) : ℝ := (1 + 1/s) / s

/-- The derivative of `Hw`: `H'(s) = -1/s^2 - 2/s^3`. -/
def Hwderiv (s : ℝ) : ℝ := -(1 / s^2) - 2 / s^3

lemma Hw_eq {s : ℝ} (hs : s ≠ 0) : Hw s = 1/s + 1/s^2 := by
  unfold Hw
  field_simp

lemma Hw_pos {s : ℝ} (hs : 0 < s) : 0 < Hw s := by
  rw [Hw_eq (ne_of_gt hs)]
  positivity

lemma Hw_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ Hw s := le_of_lt (Hw_pos hs)

lemma Hw_le_two {s : ℝ} (hs : 1 ≤ s) : Hw s ≤ 2 := by
  rw [Hw_eq (by linarith : s ≠ 0)]
  have h1 : 1/s ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h2 : 1/s^2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  linarith

lemma Hw_antitone : AntitoneOn Hw (Set.Ici 1) := by
  intro a ha b hb hab
  have ha1 : (1:ℝ) ≤ a := ha
  have hb1 : (1:ℝ) ≤ b := hb
  rw [Hw_eq (by linarith : a ≠ 0), Hw_eq (by linarith : b ≠ 0)]
  have ha0 : 0 < a := by linarith
  have e1 : 1/b ≤ 1/a := one_div_le_one_div_of_le ha0 hab
  have e2 : 1/b^2 ≤ 1/a^2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  linarith

lemma hasDerivAt_Hw {s : ℝ} (hs : s ≠ 0) : HasDerivAt Hw (Hwderiv s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + 1/s) (-(1/s^2)) s := by
    have h := (hasDerivAt_const (x := s) (c := (1:ℝ))).add (hasDerivAt_inv hs)
    convert h using 1
    · ext y; simp [one_div]
    · simp [one_div]
  have h2 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
  have h := h1.div h2 hs
  unfold Hw Hwderiv
  convert h using 1
  field_simp
  ring

lemma Hwderiv_neg {s : ℝ} (hs : 0 < s) : Hwderiv s < 0 := by
  unfold Hwderiv
  have h1 : 0 < 1/s^2 := by positivity
  have h2 : 0 < 2/s^3 := by positivity
  linarith

lemma abs_Hwderiv {s : ℝ} (hs : 0 < s) : |Hwderiv s| = 1/s^2 + 2/s^3 := by
  rw [abs_of_neg (Hwderiv_neg hs)]
  unfold Hwderiv
  ring

/-- Norm of the oscillatory factor: for `t > 0`, `‖t^{-1-iu}‖ = t^{-1}`. -/
lemma norm_cpow_neg_one_sub_I_mul (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(t:ℂ) ^ (-(1:ℂ) - Complex.I * (u:ℂ))‖ = t⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (-(1:ℂ) - Complex.I * (u:ℂ)).re = -1 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre, Real.rpow_neg_one]

/-- Norm of the oscillatory factor `t^{-iu}`: for `t > 0` it is `1`. -/
lemma norm_cpow_neg_I_mul (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(t:ℂ) ^ (-(Complex.I * (u:ℂ)))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (-(Complex.I * (u:ℂ))).re = 0 := by
    simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre, Real.rpow_zero]

end

end Work.BMF.liouville
