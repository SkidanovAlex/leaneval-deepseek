import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Commons.Analysis.Complex

/-- For `w` in the open unit disc, `(1 + w) / (1 - w)` has positive real part. -/
private lemma strip_one_add_div_one_sub_re_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < ((1 + w) / (1 - w)).re := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := (sub_eq_zero.mp h).symm
    rw [hw1] at hw
    simp at hw
  have hre : ((1 + w) / (1 - w)).re = (1 - ‖w‖^2) / Complex.normSq (1 - w) := by
    rw [Complex.div_re]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.sub_re,
      Complex.sub_im, Complex.one_im, Complex.add_im]
    have hsq : ‖w‖^2 = w.re*w.re + w.im*w.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hsq]
    ring
  rw [hre]
  apply div_pos
  · nlinarith [norm_nonneg w]
  · rw [Complex.normSq_pos]
    exact hne

theorem strip_map_mapsTo (q : ℝ) (hq : 0 < q) :
    Set.MapsTo (fun w : ℂ => (2 * q / Real.pi) * Complex.log ((1 + w) / (1 - w)))
      (Metric.ball (0 : ℂ) 1) {z : ℂ | |z.im| < q} := by
  intro w hw
  simp only [Metric.mem_ball, dist_zero_right] at hw
  have hzre : 0 < ((1 + w) / (1 - w)).re := strip_one_add_div_one_sub_re_pos hw
  have hargtop : ((1 + w) / (1 - w)).arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  have hargbot : -(Real.pi / 2) < ((1 + w) / (1 - w)).arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzre)
  have hargabs : |((1 + w) / (1 - w)).arg| < Real.pi / 2 := abs_lt.mpr ⟨hargbot, hargtop⟩
  have hcpos : 0 < 2 * q / Real.pi := by positivity
  simp only [Set.mem_ofPred_eq]
  have hcast : (2 * (q : ℂ) / (Real.pi : ℂ)) = ((2 * q / Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  have him : ((2 * q / Real.pi) * Complex.log ((1 + w) / (1 - w))).im
      = (2 * q / Real.pi) * ((1 + w) / (1 - w)).arg := by
    rw [hcast, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.log_im]
    ring
  rw [him, abs_mul, abs_of_pos hcpos]
  calc (2 * q / Real.pi) * |((1 + w) / (1 - w)).arg|
      < (2 * q / Real.pi) * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left hargabs hcpos
    _ = q := by field_simp

end Commons.Analysis.Complex