-- Copied verbatim from `Submission.Work.Cohomology.pd_union_hit`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.pd_mvdelta_apply
import Submission.Work.Cohomology.pd_crux_weak2
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.MVSequence
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.pd_localFundClass_natural
import Submission.Work.ThomBordism.Port.PdUnionHitZero
import Submission.Work.ThomBordism.Port.PdUnionHitPos

namespace Work.Cohomology

theorem pd_union_hit {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) :
    ∀ y : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).homology m,
      ∃ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
        (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K)).homology k),
        goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x = y := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hk : k = N := hkm
    subst hk
    exact pd_union_hit_zero hU hV hI hUU hVV hII
  · exact pd_union_hit_pos hU hV hI hUU hVV hII k m hkm hm

end Work.Cohomology
