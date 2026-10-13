import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux
import Submission.Work.DSEQ0.isIso_psiUnitHom

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSEQ0

universe u

/-- The canonical isomorphism `𝒪_X ≅ secSheaf ⊤` (the structure sheaf of `X` with the pushforward
of the structure sheaf of the open `⊤`). -/
noncomputable def psiUnit (X : AlgebraicGeometry.Scheme.{u}) :
    SheafOfModules.unit X.ringCatSheaf ≅ Work.DSF1.secSheaf (⊤ : X.Opens) := by
  haveI := isIso_psiUnitHom X
  exact asIso (psiUnitHom X)

lemma psiUnit_hom_eq (X : AlgebraicGeometry.Scheme.{u}) :
    (psiUnit X).hom = psiUnitHom X := rfl

end Work.DSEQ0
