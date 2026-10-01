/-
# Area 7 — antitonicity of the density weight `Wf` off `0`

`Wf(λ) = w(λ) = λ/(e^{73λ/30} - e^{16λ/15})` is Heath-Brown's density weight (HB §11).  It is
non-increasing on all of `ℝ \ {0}` (not merely on `(0,∞)`): writing it in integral form,

  `w(λ) = 1 / ∫_{16/15}^{73/30} e^{tλ} dt   (λ ≠ 0)`,

the integrand `t ↦ e^{tλ}` is, for every `t ≥ 16/15 > 0`, an increasing function of `λ`; hence the
integral is increasing in `λ` and its reciprocal is decreasing.  No sign hypothesis on `λ` is
needed, only that the integration range lies in `[0,∞)` and that `λ ≠ 0`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs

noncomputable section

namespace Work.A7

open Work.LinnikContract

/-- The integral form of the denominator of the density weight: with `A = 73/30 > B = 16/15` and
`x ≠ 0`, `∫_B^A e^{tx} dt = (e^{Ax} - e^{Bx})/x`.  (Substitute `u = tx`.) -/
private lemma exp_int_eq (x : ℝ) (hx : x ≠ 0) :
    (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x))
      = (Real.exp ((73:ℝ)/30 * x) - Real.exp ((16:ℝ)/15 * x)) / x := by
  rw [intervalIntegral.integral_comp_mul_right (fun y : ℝ => Real.exp y) hx]
  rw [integral_exp]
  simp only [smul_eq_mul]
  ring

/-- `Wf x` is the reciprocal of `∫_{16/15}^{73/30} e^{tx} dt` for `x ≠ 0`; in particular it is the
reciprocal of a positive, increasing function of `x`. -/
private lemma Wf_eq (x : ℝ) (hx : x ≠ 0) :
    Work.LinnikAreas.A7.Wf x
      = 1 / (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x)) := by
  rw [Work.LinnikAreas.A7.Wf, Work.LinnikContract.wHB, exp_int_eq x hx, one_div, inv_div]

/-- **Antitonicity of the density weight off `0`.**  `Wf` is non-increasing on `ℝ \ {0}`:
for `x ≤ y` with `x, y ≠ 0` one has `Wf y ≤ Wf x`. -/
theorem Wf_antitone_ne : ∀ {x y : ℝ}, x ≤ y → x ≠ 0 → y ≠ 0 → Work.LinnikAreas.A7.Wf y ≤ Work.LinnikAreas.A7.Wf x := by
  intro x y hxy hx hy
  have hba : ((16:ℝ)/15) ≤ ((73:ℝ)/30) := by norm_num
  have hbalt : ((16:ℝ)/15) < ((73:ℝ)/30) := by norm_num
  have hcont_x : Continuous (fun t : ℝ => Real.exp (t * x)) := by fun_prop
  have hcont_y : Continuous (fun t : ℝ => Real.exp (t * y)) := by fun_prop
  -- the integrand, hence the integral `∫_B^A e^{tλ} dt`, is increasing in `λ`
  have hmono : (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x))
      ≤ (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * y)) := by
    apply intervalIntegral.integral_mono_on hba (hcont_x.intervalIntegrable _ _)
      (hcont_y.intervalIntegrable _ _)
    intro t ht
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
    exact mul_le_mul_of_nonneg_left hxy ht0
  -- and it is positive for every real parameter
  have hpos : 0 < (∫ t in ((16:ℝ)/15)..((73:ℝ)/30), Real.exp (t * x)) :=
    intervalIntegral.intervalIntegral_pos_of_pos (hcont_x.intervalIntegrable _ _)
      (fun t => Real.exp_pos _) hbalt
  rw [Wf_eq y hy, Wf_eq x hx]
  exact one_div_le_one_div_of_le hpos hmono

end Work.A7
