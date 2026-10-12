import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- The corpus localization bump `χ` is supported in the ball of radius `1/2`
(`Submission.BoseGases.chi_eq_zero_of_norm_gt`), and that ball sits inside the unit cell
`[-1/2,1/2]³` (`Work.BoseK15.chi_support_subset_unitCell`).  Hence the set integral over the
unit cell is the full Lebesgue integral of `χ²`, which is `1` by the `L²` normalisation
`Submission.BoseGases.chi_L2`. -/
theorem integral_unitCell_chi_sq :
    ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 = 1 := by
  have hzero : ∀ x ∉ Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 = 0 := by
    intro x hx
    have hx0 : Submission.BoseGases.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.chi_support_subset_unitCell h)
    rw [hx0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact Submission.BoseGases.chi_L2

end Work.BoseBoxFock
