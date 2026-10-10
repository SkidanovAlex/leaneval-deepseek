import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Submission.Work.SSGRoute.H1Dual.LES
import Submission.Work.SSGRoute.H1Dual.coindRepIsoCoind
import Submission.Work.SSGRoute.H1Dual.dualCoindRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace Work.SSGRoute.H1Dual

variable {k : Type} [Field k] {G : Type} [Group G] [Fintype G]

theorem isZero_groupHomology_coindRep (V : Type) [AddCommGroup V] [Module k V] :
    IsZero (groupHomology (coindRep k G V) 1) := by
  classical
  obtain ⟨e⟩ := coindRepIsoCoind k G V
  let A : Rep k ↥(⊥ : Subgroup G) := Rep.trivial k ↥(⊥ : Subgroup G) V
  have e1 : coindRep k G V ≅ Rep.ind (⊥ : Subgroup G).subtype A :=
    e ≪≫ (Rep.indCoindIso (S := (⊥ : Subgroup G)) A).symm
  have e2 : groupHomology (coindRep k G V) 1 ≅ groupHomology A 1 :=
    (groupHomology.functor k G 1).mapIso e1 ≪≫ groupHomology.indIso (⊥ : Subgroup G) A 1
  exact isZero_of_iso e2 (isZero_groupHomology_succ_of_subsingleton A 0)

theorem isZero_groupCohomology_coindRep (V : Type) [AddCommGroup V] [Module k V] :
    IsZero (groupCohomology (coindRep k G V) 1) := by
  classical
  obtain ⟨e⟩ := coindRepIsoCoind k G V
  let A : Rep k ↥(⊥ : Subgroup G) := Rep.trivial k ↥(⊥ : Subgroup G) V
  have e2 : groupCohomology (coindRep k G V) 1 ≅ groupCohomology A 1 :=
    (groupCohomology.functor k G 1).mapIso e ≪≫ groupCohomology.coindIso A 1
  exact isZero_of_iso e2 (isZero_groupCohomology_succ_of_subsingleton A 0)

theorem isZero_groupCohomology_dualRep_coindRep (V : Type) [AddCommGroup V] [Module k V] :
    IsZero (groupCohomology (dualRep (coindRep k G V)) 1) := by
  classical
  obtain ⟨e⟩ := dualCoindRep k G V
  exact isZero_of_iso ((groupCohomology.functor k G 1).mapIso e)
    (isZero_groupCohomology_coindRep (k := k) (G := G) (Module.Dual k V))

end Work.SSGRoute.H1Dual
