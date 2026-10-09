/-
Import umbrella for the (U2) Kummer-at-the-henselian-level node
(`Work.SSGRoute.E1aClean.LeadPhiUnr.henselUnit_pow_mul_localUnits_of_inertiaFixedRoot`) and for
its auxiliary lemmas.  It collects, in one place, everything the statements and proofs of the
node need:

* the shared `SSGRoute` vocabulary (`IsInertia`, `decomp`, …);
* the henselian datum `k^h = Ω^{D_A}`, `K^h = Ω^{D_A ⊓ G_K}`;
* the "decomposition field is an immediate extension" lemma
  `Commons.RingTheory.Valuation.valuation_mem_range_of_mem_decompositionField`;
* the global Kummer character `Work.SSGRoute.kummerCharZMod` and its root-independence;
* the PROVED global Kummer lemma
  `Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified`.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Commons.RingTheory.Valuation.valuation_mem_range_of_mem_decompositionField
import Submission.Work.SSGRoute.place_comap_valuationSubringAtPrime
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
