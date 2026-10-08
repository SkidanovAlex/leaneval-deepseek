/-
Area A9 (normal `p`-complement theorems): the assembly module.

`import Submission.Work.NPC.All` gives access to the whole area under one namespace `Work.NPC`:

* the definitions (`HasNormalPComplement`, `IsNormalPComplement`, `HasFrobeniusCondition`,
  `IsConjPGroup`, and the abbreviations `thompsonJ`, `centerOf`, `ZJ` of area A4's `J(P)`, `Z(P)`,
  `Z(J(P))`), from `Submission.Work.NPC.Defs`;
* the transfer engine (`hasNormalPComplement_of_hom_to_pGroup`), Burnside's theorem
  (`burnside_npc`) and the focal-subgroup corollaries, from `Submission.Work.NPC.Engine`;
* the basic API (uniqueness of the normal `p`-complement, subgroup/quotient/isomorphism
  inheritance, the Sylow-complement criterion), from `Submission.Work.NPC.Basic`,
  `Submission.Work.NPC.Complement`, `Submission.Work.NPC.Transfer`;
* **Frobenius' normal `p`-complement theorem** `Work.NPC.frobenius_npc`
  (`Submission.Work.NPC.Frobenius.frobenius_npc`), together with the four equivalent formulations
  of Frobenius' criterion (`hasFrobeniusCondition_iff_...`, `conjugacyClosed_sylow_...`,
  `hasFrobeniusCondition_of_hasNormalPComplement`).

The parked, off-critical-path statements `Work.NPC.Thompson.thompson_npc`,
`Work.NPC.ZJ.glauberman_thompson_npc` and the transfer criterion
`Work.NPC.Transfer.hasNormalPComplement_of_focalSubgroup_eq_commutator` are deliberately NOT
imported here (see `NOTES.md`, "Critical path").
-/
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Engine
import Submission.Work.NPC.Fusion
import Submission.Work.NPC.Complement
import Submission.Work.NPC.Basic.isNormalPComplement_index_eq_pow
import Submission.Work.NPC.Basic.isNormalPComplement_complement_sylow
import Submission.Work.NPC.Basic.isNormalPComplement_unique
import Submission.Work.NPC.Basic.hasNormalPComplement_mono
import Submission.Work.NPC.Basic.hasNormalPComplement_of_isPGroup
import Submission.Work.NPC.Basic.hasNormalPComplement_of_coprime
import Submission.Work.NPC.Basic.hasNormalPComplement_congr
import Submission.Work.NPC.Basic.hasNormalPComplement_quotient
import Submission.Work.NPC.Basic.hasNormalPComplement_of_normal_pPrime_quotient
import Submission.Work.NPC.Basic.hasNormalPComplement_of_surjective
import Submission.Work.NPC.Basic.isNormalPComplement_map_of_quotient
import Submission.Work.NPC.Frobenius.isConjPGroup_map_conj
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_iff_forall_le_sylow
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement
import Submission.Work.NPC.Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_subgroup
import Submission.Work.NPC.Frobenius.npc_of_conjugacyClosed_sylow
import Submission.Work.NPC.Frobenius.hasNormalPComplement_of_conjugacyClosed_sylow
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_conjugacyClosed_sylow
import Submission.Work.NPC.Frobenius.npc_of_normalizer_npc
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_normalizer_npc
import Submission.Work.NPC.Frobenius.frobenius_npc
import Submission.Work.NPC.Transfer.hasNormalPComplement_iff_exists_hom
import Submission.Work.NPC.Criterion.Necessary
import Submission.Work.NPC.Criterion.Heredity
import Submission.Work.NPC.Criterion.TransferKernel
import Submission.Work.NPC.Fpf.Aliases

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC

/-! ### Basic API -/

alias isNormalPComplement_index_eq_pow := Basic.isNormalPComplement_index_eq_pow
alias isNormalPComplement_complement_sylow := Basic.isNormalPComplement_complement_sylow
alias isNormalPComplement_unique := Basic.isNormalPComplement_unique
alias hasNormalPComplement_mono := Basic.hasNormalPComplement_mono
alias hasNormalPComplement_of_isPGroup := Basic.hasNormalPComplement_of_isPGroup
alias hasNormalPComplement_of_coprime := Basic.hasNormalPComplement_of_coprime
alias hasNormalPComplement_congr := Basic.hasNormalPComplement_congr
alias hasNormalPComplement_quotient := Basic.hasNormalPComplement_quotient
alias hasNormalPComplement_of_normal_pPrime_quotient :=
  Basic.hasNormalPComplement_of_normal_pPrime_quotient
alias hasNormalPComplement_of_surjective := Basic.hasNormalPComplement_of_surjective
alias isNormalPComplement_map_of_quotient := Basic.isNormalPComplement_map_of_quotient

/-! ### The Frobenius criterion -/

alias isConjPGroup_map_conj := Frobenius.isConjPGroup_map_conj
alias hasFrobeniusCondition_iff_forall_le_sylow := Frobenius.hasFrobeniusCondition_iff_forall_le_sylow
alias hasFrobeniusCondition_of_hasNormalPComplement :=
  Frobenius.hasFrobeniusCondition_of_hasNormalPComplement
alias conjugacyClosed_sylow_of_hasFrobeniusCondition :=
  Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition
alias hasFrobeniusCondition_subgroup := Frobenius.hasFrobeniusCondition_subgroup
alias npc_of_conjugacyClosed_sylow := Frobenius.npc_of_conjugacyClosed_sylow
alias hasNormalPComplement_of_conjugacyClosed_sylow :=
  Frobenius.hasNormalPComplement_of_conjugacyClosed_sylow
alias hasFrobeniusCondition_of_conjugacyClosed_sylow :=
  Frobenius.hasFrobeniusCondition_of_conjugacyClosed_sylow
alias npc_of_normalizer_npc := Frobenius.npc_of_normalizer_npc
alias hasFrobeniusCondition_of_normalizer_npc := Frobenius.hasFrobeniusCondition_of_normalizer_npc
alias frobenius_npc := Frobenius.frobenius_npc
alias hasNormalPComplement_iff_exists_hom := Transfer.hasNormalPComplement_iff_exists_hom

/-! ### The transfer criterion `P* = ⁅P, P⁆` (the *necessary* direction and its heredity)

The deep converse (the criterion `P* = ⁅P, P⁆ ⟹ HasNPC`) is not part of the delivered area; its
reduction to Tate's theorem is recorded in `Parked/Reduction.lean.parked` and `HINTS.md` §2.  What
is delivered here is the easy direction and the transfer-kernel structure, which complete the list
of characterizations of `HasNormalPComplement` by the focal subgroup of a Sylow. -/

alias focalSubgroup_eq_commutator_of_hasNormalPComplement :=
  Criterion.focalSubgroup_eq_commutator_of_hasNormalPComplement
alias commutator_inf_eq_commutator_of_hasNormalPComplement :=
  Criterion.commutator_inf_eq_commutator_of_hasNormalPComplement
alias isConj_in_of_hasNormalPComplement := Criterion.isConj_in_of_hasNormalPComplement
alias focalSubgroup_eq_commutator_iff_transferKernel :=
  Criterion.focalSubgroup_eq_commutator_iff_transferKernel
alias isPGroup_quotient_transferKernel := Criterion.isPGroup_quotient_transferKernel
alias hasNormalPComplement_of_transferKernel := Criterion.hasNormalPComplement_of_transferKernel
alias commutator_inf_eq_of_focalSubgroup_eq_commutator :=
  Criterion.commutator_inf_eq_of_focalSubgroup_eq_commutator
alias commutator_inf_eq_commutator_of_focalSubgroup_eq_commutator :=
  Criterion.commutator_inf_eq_commutator_of_focalSubgroup_eq_commutator

end Work.NPC

