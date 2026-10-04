import Mathlib
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped BigOperators

/-- The character `fourierExp m` is invariant under translation by an integer vector.  Indeed
`fourierExp m (x + k) = exp (2πi (m·x + m·k))` and `m·k ∈ ℤ`, so `exp (2πi m·k) = 1`. -/
theorem fourierExp_shift_iVec {ι : Type*} [Fintype ι] (m k : ι → ℤ) (x : ι → ℝ) :
    Work.Diff.STE.fourierExp m (x + Work.Diff.STE.iVec k) = Work.Diff.STE.fourierExp m x := by
  -- the phase shifts by the integer `∑ᵢ mᵢ kᵢ`
  have hsum : (∑ i, (m i : ℂ) * ((x + Work.Diff.STE.iVec k) i : ℂ))
      = (∑ i, (m i : ℂ) * (x i : ℂ)) + ((∑ i, m i * k i : ℤ) : ℂ) := by
    simp only [Pi.add_apply, Work.Diff.STE.iVec]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Work.Diff.STE.fourierExp]
  rw [hsum]
  -- `exp (2πi S + 2πi N) = exp (2πi S) * 1 = exp (2πi S)` for `N = ∑ᵢ mᵢ kᵢ ∈ ℤ`
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((∑ i, ↑(m i) * ↑(x i)) + ↑(∑ i, m i * k i))
        = (2 : ℂ) * ↑Real.pi * Complex.I * (∑ i, ↑(m i) * ↑(x i))
          + ↑(∑ i, m i * k i) * (2 * ↑Real.pi * Complex.I) by ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end Work.Diff.STE.B3
