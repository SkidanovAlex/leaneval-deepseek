import Mathlib
import Submission.Work.LinnikContract.Areas

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Work.LinnikContract

/-- The integral form of the denominator of the density weight: with `A = 73/30 > B = 16/15` and
`x ≠ 0`,
`∫_B^A e^{tx} dt = (e^{Ax} - e^{Bx})/x`.  (Substitute `u = tx`.) -/
private lemma exp_int_eq (x : ℝ) (hx : x ≠ 0) :
    (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x))
      = (Real.exp ((73:ℝ)/30 * x) - Real.exp ((16:ℝ)/15 * x)) / x := by
  rw [intervalIntegral.integral_comp_mul_right (fun y : ℝ => Real.exp y) hx]
  rw [integral_exp]
  simp only [smul_eq_mul]
  ring

/-- `wHB x` is the reciprocal of `∫_B^A e^{tx} dt` (for `x ≠ 0`); in particular it is the
reciprocal of a positive, increasing function of `x`. -/
private lemma wHB_eq (x : ℝ) (hx : x ≠ 0) :
    wHB x = 1 / (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x)) := by
  rw [wHB, exp_int_eq x hx, one_div, inv_div]

/-- **Heath-Brown §11, monotonicity of the density weight.**  The weight `w(λ) = λ/(e^{Aλ} - e^{Bλ})`
of HB (11.3) (here `A = 73/30 > B = 16/15`) is decreasing in `λ > 0`: indeed
`(e^{Aλ}-e^{Bλ})/λ = ∫_B^A e^{tλ} dt` is increasing in `λ`.  This is used to compare the weight of
the minimal zero `λ^{(χ)} = lamChar χ` with the weight of any chosen zero `λ(ρ) ≥ λ^{(χ)}` of the same
character when transferring the weighted zero-density bound of HB Lemma 11.1 to the form required by
the frozen contract (`DensityCert`). -/
theorem wHB_antitone : ∀ {a b : ℝ}, 0 < a → a ≤ b → Work.LinnikContract.wHB b ≤ Work.LinnikContract.wHB a := by
  intro a b ha hab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hab)
  have hba : ((16:ℝ)/15) ≤ ((73:ℝ)/30) := by norm_num
  have hbalt : ((16:ℝ)/15) < ((73:ℝ)/30) := by norm_num
  have hcont_a : Continuous (fun t : ℝ => Real.exp (t * a)) := by fun_prop
  have hcont_b : Continuous (fun t : ℝ => Real.exp (t * b)) := by fun_prop
  -- the integrand, and hence the integral `∫_B^A e^{tλ} dt = (e^{Aλ}-e^{Bλ})/λ`, is increasing in `λ`
  have hmono : (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * a))
      ≤ (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * b)) := by
    apply intervalIntegral.integral_mono_on hba (hcont_a.intervalIntegrable _ _)
      (hcont_b.intervalIntegrable _ _)
    intro t ht
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
    exact mul_le_mul_of_nonneg_left hab ht0
  -- the integral is positive on `λ > 0`
  have hpos : 0 < (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * a)) :=
    intervalIntegral.intervalIntegral_pos_of_pos (hcont_a.intervalIntegrable _ _)
      (fun t => Real.exp_pos _) hbalt
  rw [wHB_eq b hb0, wHB_eq a ha0]
  exact one_div_le_one_div_of_le hpos hmono

end Work.LinnikAreas.Density4
