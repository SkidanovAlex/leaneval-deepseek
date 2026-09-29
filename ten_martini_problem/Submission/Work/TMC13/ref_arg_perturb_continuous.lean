import Mathlib
import Submission.Work.TMComp.RotBasics.Defs

namespace Work.TMC13

open Work.TMComp.RotBasics

/-- The half-turn parametrization `t ↦ (cos πt, sin πt)` of the unit circle is continuous. -/
theorem continuous_vc : Continuous vc := by
  have h : vc = fun t : ℝ =>
      (Real.cos (Real.pi * t) : ℂ) + (Real.sin (Real.pi * t) : ℂ) * Complex.I := by
    funext t
    apply Complex.ext <;> simp [vc, -Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [h]
  fun_prop

/-- When `‖r‖ < 1`, the point `1 + r·vc(-2t)` always has positive real part (it stays inside
the open disc of radius `1` about `1`), hence lies in the slit plane where `arg` is analytic. -/
theorem re_one_add_mul_vc_pos {r : ℂ} (hr : ‖r‖ < 1) (t : ℝ) :
    0 < (1 + r * vc (-2 * t)).re := by
  have hw : ‖vc (-2 * t)‖ = 1 := vc_norm _
  have h1 : -‖r * vc (-2 * t)‖ ≤ (r * vc (-2 * t)).re := by
    have h := Complex.abs_re_le_norm (r * vc (-2 * t))
    rw [abs_le] at h
    linarith [h.1]
  have h2 : ‖r * vc (-2 * t)‖ = ‖r‖ := by rw [norm_mul, hw, mul_one]
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem ref_arg_perturb_continuous {r : ℂ} (hr : ‖r‖ < 1) :
    Continuous (fun t : ℝ => Complex.arg (1 + r * Work.TMComp.RotBasics.vc (-2 * t))) := by
  have hf : Continuous (fun t : ℝ => 1 + r * Work.TMComp.RotBasics.vc (-2 * t)) := by
    have hvc : Continuous Work.TMComp.RotBasics.vc := continuous_vc
    fun_prop
  exact Complex.continuousOn_arg.comp_continuous hf
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_add_mul_vc_pos hr t)))

end Work.TMC13
