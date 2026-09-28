
-- The gluing step for the `Good` predicate, assembled inside the clash-free chain.
--
-- `Work.Cohomology.pd_good_union` (the original file) does not compile: it imports both
-- `Work.Cohomology.pd_union_hit` (whose closure declares `Work.Cohomology.pdRelSub_inter` in
-- `pd_glue3`) and `Work.Cohomology.relCohomology_vanishing_of_compact` (whose closure declares the
-- *specialized* duplicate `Work.Cohomology.pdRelSub_inter` in `localClass_union_injective`); the two
-- declarations clash, so no module can import both.  This file assembles the same gluing from the
-- ported `pd_union_hit` / `pd_union_kill_chart` plus the vanishing lemma, and supplies the vanishing
-- from the self-contained fork `Submission.Work.Projective.GoodCp2.fork`
-- (`chart_relCohomology_vanishing_of_compact`), which does not use the clashing chain.
import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.ThomBordism.Port.PdUnionHit
import Submission.Work.ThomBordism.Port.PdUnionKillChart
import Submission.Work.ThomBordism.Port.ForkChartRelCohVanishing

set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The gluing step for `Good`, with the vanishing hypothesis.**  `Good N c U → Good N c V →
Good N c (U ∩ V) → (H^k_c(U∩V) = 0 for k > N) ⟹ Good N c (U ∪ V)`. -/
theorem glue_of_vanishing {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (hvan : ∀ k, N < k → ∀ K : Set M, K ⊆ U ∩ V → IsCompact K →
        ∃ K' : Set M, K ⊆ K' ∧ K' ⊆ U ∩ V ∧ IsCompact K' ∧
          Subsingleton ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) K')).homology k)) :
    Good N c (U ∪ V) (hU.union hV) :=
  fun k m hkm =>
    ⟨pd_union_hit hU hV hI hUU hVV hII k m hkm,
     pd_union_kill_chart hU hV hI hUU hVV hII hvan k m hkm⟩

/-- **The gluing step for `Good` when the intersection lies inside one chart.**  The vanishing
hypothesis of `glue_of_vanishing` is then supplied by
`Work.Cohomology.chart_relCohomology_vanishing_of_compact` (the importable fork). -/
theorem glue_of_chart {M : TopCat} [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (cc : M) (hsrc : U ∩ V ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source)
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI) :
    Good N c (U ∪ V) (hU.union hV) :=
  glue_of_vanishing hU hV hI hUU hVV hII
    (fun k hk K hK hKc =>
      chart_relCohomology_vanishing_of_compact cc (U ∩ V) hsrc hI k hk K hK hKc)

end

end Work.Cohomology
