import Mathlib

namespace Work.Pert.PinLogDev

/-- The principal branch of the complex logarithm is multiplicative on `z * (1 + w)` when
`z` lies in the open right half-plane and `‖w‖ ≤ 1/2`.

Indeed `z.arg ∈ (-π/2, π/2)` because `0 < z.re`, and `re (1 + w) ≥ 1 - ‖w‖ ≥ 1/2 > 0` gives
`(1 + w).arg ∈ (-π/2, π/2)`, so the two arguments add up to a value in `(-π, π) ⊆ Ioc (-π) π`,
which is exactly the hypothesis of `Complex.log_mul`. -/
theorem log_mul_one_add_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : ‖w‖ ≤ 1 / 2) :
    Complex.log (z * (1 + w)) = Complex.log z + Complex.log (1 + w) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hwre : 0 < (1 + w).re := by
    have hb := abs_le.mp (Complex.abs_re_le_norm w)
    simp only [Complex.add_re, Complex.one_re]
    linarith [hb.1]
  have h1w0 : (1 + w) ≠ 0 := by
    intro h; rw [h] at hwre; simp at hwre
  rw [Complex.log_mul hz0 h1w0]
  have hza : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hz)
  have hzb : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have hwa : -(Real.pi / 2) < (1 + w).arg :=
    Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hwre)
  have hwb : (1 + w).arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hwre)
  simp only [Set.mem_Ioc]
  constructor <;> linarith [Real.pi_pos]

end Work.Pert.PinLogDev
