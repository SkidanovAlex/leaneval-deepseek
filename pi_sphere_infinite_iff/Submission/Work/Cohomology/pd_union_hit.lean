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
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.pd_localFundClass_natural
import Submission.Work.Cohomology.pd_union_hit_zero
import Submission.Work.Cohomology.pd_union_hit_pos

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
