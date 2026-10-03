import Submission.Work.ORLyndon.Fox
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Magnus
import Submission.Work.ORLyndon.ProjDim
import Submission.Work.ORLyndon.DiagTensor
import Submission.Work.ORLyndon.GlobalDimTransfer
import Submission.Work.ORLyndon.GlobalDimRes
import Submission.Work.ORLyndon.Fox.fundamental_identity
import Submission.Work.ORLyndon.Fox.fundamental_identity_map
import Submission.Work.ORLyndon.augIdeal_eq_span
import Submission.Work.ORLyndon.augIdealIn_eq_span
import Submission.Work.ORLyndon.lyndonDelta_range_eq_augIdeal
import Submission.Work.ORLyndon.lyndon_exact_relationModuleMap
import Submission.Work.ORLyndon.relationModuleMap_injective
import Submission.Work.ORLyndon.projective_quotient_span_of_pow_eq_one
import Submission.Work.ORLyndon.HasProjDimLE_of_linearEquiv
import Submission.Work.ORLyndon.HasProjDimLE_mono
import Submission.Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE
import Submission.Work.ORLyndon.globalDim_le_of_forall_projectiveDimension
import Submission.Work.ORLyndon.globalDim_le_of_ringEquiv
import Submission.Work.ORLyndon.lyndon_ker_theta_le
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.mem_span_of_coset_sums
import Submission.Work.ORLyndon.lyndon_independence
import Submission.Work.ORLyndon.lyndon_ker_theta_of_independence
import Submission.Work.ORLyndon.lyndon_range_theta
import Submission.Work.ORLyndon.lyndon_ker_delta_free
import Submission.Work.ORLyndon.LyndonFree
import Submission.Work.ORLyndon.magnus_fox_decomposition
import Submission.Work.ORLyndon.magnusTwoTerm_of_lyndon
import Submission.Work.ORLyndon.LyndonCombinatorics
import Submission.Work.ORLyndon.hasProjDimLE_trivial_of_lyndon
import Submission.Work.ORLyndon.hasProjDimLE_of_trivial
import Submission.Work.ORLyndon.Tor1Vanishes_projective
import Submission.Work.ORLyndon.MagnusMiddle
import Submission.Work.ORLyndon.LyndonFlatness
import Submission.Work.ORLyndon.BalTensorQuotDefs
import Submission.Work.ORLyndon.relationModule_ident
import Submission.Work.ORLyndon.lyndon_fourTerm_exact
import Submission.Work.ORLyndon.balTensor_quot_equiv
import Submission.Work.ORLyndon.relationModule_balTensor

import Submission.Work.ORLyndon.mmConnDefs
import Submission.Work.ORLyndon.mmBaseHom_comp_mk
import Submission.Work.ORLyndon.mmBaseHom_transport
import Submission.Work.ORLyndon.mmBaseHom_injective
import Submission.Work.ORLyndon.range_mmBaseHom_ncl
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.lyndonIndependence_of_pow_of_step
import Submission.Work.ORLyndon.botPart_mul
import Submission.Work.ORLyndon.ann_rootVec_of_level_bot
import Submission.Work.ORLyndon.mmLo_ne_mmHi_or_exists_letter
import Submission.Work.ORLyndon.level_ge_of_foxD_eq_zero
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm_bot

import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters
import Submission.Work.ORLyndon.mmBotSym_mem_relatorLetters
import Submission.Work.ORLyndon.CLInvDefs
import Submission.Work.ORLyndon.CLSym
import Submission.Work.ORLyndon.CLStepA
import Submission.Work.ORLyndon.isCyclicallyReducedRelator_rootW
import Submission.Work.ORLyndon.CLAssembly
-- import-hygiene copy of `Work.OROneRel.foxD_zeta_of_ne` (no `RhoRewrite`): see `README.md`
import Submission.Work.ORLyndon.foxD_zeta_of_ne_clean
-- import-hygiene copy of `Work.OROneRel.relatorLetters_pow` (no `weinbaum_at`): see `README.md`
import Submission.Work.ORLyndon.relatorLetters_pow_clean

-- the unconditional Cohen--Lyndon route (`CASE2INPUT_LEAD.md`) and its consequences
import Submission.Work.ORLyndon.CLDirect.All
import Submission.Work.ORLyndon.lyndon_independence_of_pow
import Submission.Work.ORLyndon.lyndonIdentity_of_pow

-- the set-indexed `annAt` formulation of the Cohen--Lyndon descent (see `README.md`)
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.annAt_of_epsZero
import Submission.Work.ORLyndon.annAt_of_epsZero_strong
import Submission.Work.ORLyndon.annChain

/-!
# Area N3: the Lyndon identity theorem and `gl.dim ≤ 2`

Umbrella module for the chapter `Submission/Work/ORLyndon`: the Fox calculus on free groups, the
Lyndon complex of a one-relator presentation and its exactness, the hypothesis structures packaging
Lyndon's identity theorem and the two-term (Magnus) form, and the machinery giving
`globalDim K[G] ≤ 2`.  See `README.md` in this directory for the interface.
-/
