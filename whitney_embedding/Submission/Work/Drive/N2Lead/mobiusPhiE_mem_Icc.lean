import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.modelArc_re_strictMono

namespace Work.Drive.N2Lead

/-- The polar angle `φE = Complex.arg (Complex.sqrt ((-η) + m·i))` of the endpoint of the pinned top
arc always lies in `[-π/2, π/2]`.

Proof plan: `Complex.sqrt z` is by definition `z ^ (2⁻¹ : ℂ)`, so
`(Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re)/2) ≥ 0` by `Complex.cpow_inv_two_re` (or the
workspace lemma `complex_sqrt_re` of `Submission/Work/Drive/N2Lead/modelArc_re_strictMono.lean`);
the two inequalities then follow from `Complex.abs_arg_le_pi_div_two_iff`, or from
`Complex.neg_pi_div_two_le_arg_iff` and `Complex.arg_le_pi_div_two_iff`. -/
theorem mobiusPhiE_mem_Icc (η m : ℝ) :
    -(Real.pi / 2) ≤ Work.Drive.N2Lead.mobiusPhiE η m ∧
      Work.Drive.N2Lead.mobiusPhiE η m ≤ Real.pi / 2 := by
  -- The principal square root of any complex number has non-negative real part.
  have h0 : 0 ≤ (Complex.sqrt ((-η : ℂ) + (m : ℂ) * Complex.I)).re := by
    rw [complex_sqrt_re]
    exact Real.sqrt_nonneg _
  -- For a complex number with non-negative real part the polar angle lies in `[-π/2, π/2]`.
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr h0
  rw [mobiusPhiE]
  exact abs_le.mp h

end Work.Drive.N2Lead
