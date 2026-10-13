import Mathlib
import Submission.Work.DSF1.Sheaf.exists_cechSheafPresheaf
import Submission.Work.DSEQ0.cechTrivAll_sectionsV
import Submission.Work.DSEQ0.cechSh_sectionsV_iso
import Submission.Work.DSF1.Sheaf.cechTrivAll_of_restrP

namespace Work.DSF1.Sheaf

universe u

theorem cechTrivAt_sectionsV (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (W : X.Opens) (i₀ : ι) (hW : W ≤ U i₀) (n : ℕ) :
    Work.DSF1.Sheaf.CechTrivAt
      ((CategoryTheory.Functor.mapHomologicalComplex (Work.DSEQ0.sectionsV X W) (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X))) n := by
  obtain ⟨e, -, -⟩ := Work.DSEQ0.cechSh_sectionsV_iso X U W
  exact Work.DSF1.Sheaf.cechTrivAll_of_iso e (Work.DSEQ0.cechTrivAll_sectionsV X U W i₀ hW) n

end Work.DSF1.Sheaf
