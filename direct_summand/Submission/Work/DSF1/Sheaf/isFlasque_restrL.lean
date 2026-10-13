import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafTerm

universe u

namespace Work.DSF1.Sheaf

open CategoryTheory

theorem isFlasque_restrL {X : AlgebraicGeometry.Scheme.{u}}
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsFlasque P) (T : X.Opens) :
    TopCat.Presheaf.IsFlasque (Work.DSF1.Sheaf.restrL P T) := by
  refine ⟨fun {U V} i => ?_⟩
  exact hP.epi (homOfLE (inf_le_inf_left T (leOfHom i.unop))).op

end Work.DSF1.Sheaf
