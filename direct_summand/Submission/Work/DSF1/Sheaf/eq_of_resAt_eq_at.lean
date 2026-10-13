import Mathlib
import Submission.Work.DSF1.Sheaf.SSEBasic

open CategoryTheory AlgebraicGeometry

universe u

namespace Work.DSF1.Sheaf

theorem eq_of_resAt_eq_at {X : AlgebraicGeometry.Scheme.{u}}
    (M : SheafOfModules X.ringCatSheaf) {ι : Type u} (W : ι → X.Opens) (U : X.Opens)
    (hcov : iSup W = U) (x y : Work.DSF1.Sheaf.sectionsAt M U)
    (h : ∀ i, Work.DSF1.Sheaf.resAt M ((le_iSup W i).trans (le_of_eq hcov)) x =
      Work.DSF1.Sheaf.resAt M ((le_iSup W i).trans (le_of_eq hcov)) y) : x = y := by
  exact TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) W U
    (fun i => homOfLE ((le_iSup W i).trans (le_of_eq hcov))) (le_of_eq hcov.symm) x y h

end Work.DSF1.Sheaf
