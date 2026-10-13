import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs

namespace Work.DSF1.Sheaf

universe u

theorem cechTrivAt_iff_homology (K : CochainComplex AddCommGrpCat.{u} ℕ) (p : ℕ) :
    Work.DSF1.Sheaf.CechTrivAt K p ↔
      CategoryTheory.Limits.IsZero (HomologicalComplex.homology K (p + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology K (p + 1)]
  rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2)
    ((ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk p (p + 1) (by ring)))
    ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (p + 1) (p + 2) (by ring)))]
  rw [CategoryTheory.ShortComplex.ab_exact_iff]
  unfold Work.DSF1.Sheaf.CechTrivAt
  rfl

end Work.DSF1.Sheaf
