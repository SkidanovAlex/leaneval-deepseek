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

/-- The corpus χ vanishes off the unit cell (`Work.BoseK15.chi_support_subset_unitCell`,
the support form of `χ` being a bump of radius `1/2`), hence the set integral over the
unit cell of `χ · cos⟪p,·⟫` is the full-space integral defining `χ̂`. -/
theorem integral_unitCell_chi_cos (p : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in Work.BoseB4.unitCell, Submission.BoseGases.chi x * Real.cos (inner ℝ p x)
      = Work.BoseK15.corpusBox.hatChi p := by
  rw [Work.BoseB4.BoxData.hatChi]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp
  · intro x hx
    have h0 : Submission.BoseGases.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.chi_support_subset_unitCell (Function.mem_support.mpr h))
    rw [h0, zero_mul]

end Work.BoseBoxFock
