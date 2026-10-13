import Mathlib
import Submission.Work.DSF1.Sheaf.SSEBasic

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry

universe u

theorem exists_glue_compatible_at {X : AlgebraicGeometry.Scheme.{u}}
    (M : SheafOfModules X.ringCatSheaf) {ι : Type u} (W : ι → X.Opens) (U : X.Opens)
    (hcov : iSup W = U) (s : ∀ i, Work.DSF1.Sheaf.sectionsAt M (W i))
    (hcompat : ∀ i j, Work.DSF1.Sheaf.resAt M (inf_le_left : W i ⊓ W j ≤ W i) (s i) =
      Work.DSF1.Sheaf.resAt M (inf_le_right : W i ⊓ W j ≤ W j) (s j)) :
    ∃ x : Work.DSF1.Sheaf.sectionsAt M U,
      ∀ i, Work.DSF1.Sheaf.resAt M ((le_iSup W i).trans (le_of_eq hcov)) x = s i := by
  have hcover : U ≤ iSup W := le_of_eq hcov.symm
  have hc : TopCat.Presheaf.IsCompatible
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj W s := by
    intro i j
    exact hcompat i j
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing'
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (X := X.toPresheafedSpace)
      W U (fun i => homOfLE ((le_iSup W i).trans (le_of_eq hcov))) hcover s hc
  exact ⟨x, hx⟩

end Work.DSF1.Sheaf
