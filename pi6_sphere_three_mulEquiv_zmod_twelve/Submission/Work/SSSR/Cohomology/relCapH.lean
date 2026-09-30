import Mathlib
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relChainsProjective
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
namespace Work.SSSR.Cohomology

noncomputable section

/-! ## The comparison iso is the canonical one -/

/-- The general form of the canonicality of the comparison of a colimit with the colimit computed
degreewise: composing with the projection out of a colimit cocone and the comparison iso
`isoOfNatIso` of an isomorphism of diagrams gives the target projection. -/
theorem coconePointUniqueUpToIso_comp_isoOfNatIso_ι {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G]
    (s : Cocone F) (P : IsColimit s) (w : F ≅ G) (j : J) :
    s.ι.app j ≫ ((P.coconePointUniqueUpToIso (colimit.isColimit F)) ≪≫
        (HasColimit.isoOfNatIso w)).hom
      = w.hom.app j ≫ colimit.ι G j := by
  rw [Iso.trans_hom, ← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact HasColimit.isoOfNatIso_ι_hom w j

set_option backward.isDefEq.respectTransparency true

end

end Work.SSSR.Cohomology
