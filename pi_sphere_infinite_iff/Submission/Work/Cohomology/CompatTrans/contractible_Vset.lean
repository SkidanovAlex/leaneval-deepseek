import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Work.Cohomology

/-- The set `Vset p q` is the product of the two caps. -/
lemma Vset_eq_prod (p q : ℕ) : (Vset p q : Set (PSph p q)) = capA p ×ˢ capA q := by
  ext z
  simp only [Vset, Set.mem_prod, Set.mem_setOf_eq, Set.mem_ofPred_eq]

/-- `↥(Vset p q)` is homeomorphic to the product of the two contractible caps. -/
def VsetHomeo (p q : ℕ) : ↥(Vset p q) ≃ₜ (↥(capA p) × ↥(capA q)) :=
  (Homeomorph.setCongr (Vset_eq_prod p q)).trans (Homeomorph.Set.prod _ _)

theorem contractible_Vset (p q : ℕ) : ContractibleSpace ↥(Vset p q) := by
  haveI hp : ContractibleSpace ↥(capA p) := contractibleSpace_capA p
  haveI hq : ContractibleSpace ↥(capA q) := contractibleSpace_capA q
  exact Homeomorph.contractibleSpace (VsetHomeo p q)

end Work.Cohomology
