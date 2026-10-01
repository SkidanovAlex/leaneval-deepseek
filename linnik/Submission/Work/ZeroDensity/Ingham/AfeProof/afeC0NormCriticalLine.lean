import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeSelf.Defs
import Submission.Work.ZeroDensity.Ingham.chi_eq_gamma_sin
import Submission.Work.ZeroDensity.Ingham.norm_zetaChi_critical
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeAux

namespace Work.ZeroDensity.Ingham.AfeProof

open Complex
open Work.ZeroDensity.Ingham

noncomputable section

/-- `cls t ≠ 0` at the critical line point. -/
lemma cls_ne_zero (t : ℝ) : cls t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [cls_re] at this
  simp at this

/-- Scalar factor `(s/π)·(2π)^s` of the resonance identity is nonzero. -/
lemma afeGauge_ne_zero (t : ℝ) :
    (cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t) ≠ 0 := by
  refine mul_ne_zero (div_ne_zero (cls_ne_zero t) ?_) ?_
  · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (cls_ne_zero t)).mpr
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

/-- On the critical line, the resonance identity solved for `c₀`:
`c₀(s) = χ(s) / ((s/π)·(2π)^s)`. -/
lemma afeC0_eq_resonance (t : ℝ) :
    afeC0 (cls t) =
      zetaChi (cls t) / ((cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)) := by
  refine (eq_div_iff (afeGauge_ne_zero t)).mpr ?_
  rw [afe_resonance (cls_re_pos t) (cls_re_lt_one t), mul_comm]

/-- `‖c₀‖` on the critical line: `‖c₀(1/2+it)‖ = π / (√(2π)·‖1/2+it‖)`. -/
lemma norm_afeC0_cls (t : ℝ) :
    ‖afeC0 (cls t)‖ = Real.pi / (Real.sqrt (2 * Real.pi) * ‖cls t‖) := by
  rw [afeC0_eq_resonance t, norm_div, norm_afeGauge t, norm_zetaChi_critical t,
    one_div_div, mul_comm ‖cls t‖ (Real.sqrt (2 * Real.pi))]

/-- The critical-line point satisfies `‖1/2 + it‖ ≤ 2t` for `t ≥ 1`. -/
lemma norm_cls_le_two_mul {t : ℝ} (ht : 1 ≤ t) : ‖cls t‖ ≤ 2 * t := by
  rw [norm_cls]
  have h1 : Real.sqrt (1 / 4 + t ^ 2) ≤ Real.sqrt ((2 * t) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [ht])
  rwa [Real.sqrt_sq (by linarith)] at h1

theorem afeC0NormCriticalLine {t : ℝ} (ht : 1 ≤ t) :
    Real.pi / (2 * Real.sqrt (2 * Real.pi)) / t ≤
      ‖Work.ZeroDensity.Ingham.afeC0 ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hsqrtpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hclspos : 0 < ‖cls t‖ := norm_pos_iff.mpr (cls_ne_zero t)
  rw [show ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = cls t from rfl, norm_afeC0_cls t]
  rw [show Real.pi / (2 * Real.sqrt (2 * Real.pi)) / t
        = Real.pi / (2 * Real.sqrt (2 * Real.pi) * t) by ring]
  apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (mul_pos hsqrtpos hclspos)
  have h := mul_le_mul_of_nonneg_left (norm_cls_le_two_mul ht) (le_of_lt hsqrtpos)
  nlinarith [h]

end

end Work.ZeroDensity.Ingham.AfeProof
