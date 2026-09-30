import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_union_hit
import Submission.Work.Cohomology.pd_union_kill_chart

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

/-- **The gluing step for `Good`, with the vanishing hypothesis.**

`Good N c U → Good N c V → Good N c (U ∩ V) → (H^k_c(U∩V) = 0 for k > N) → Good N c (U ∪ V)`.

Both clauses are available: the surjectivity clause is `pd_union_hit` (proved for all `(k,m)`),
and the injectivity clause is `pd_union_kill_chart`, which handles `m ≥ 1` by `pd_union_kill_pos`
and `m = 0` with the vanishing hypothesis. -/
theorem glue_of_vanishing {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (hvan : ∀ k, N < k → ∀ K : Set M, K ⊆ U ∩ V → IsCompact K →
        ∃ K' : Set M, K ⊆ K' ∧ K' ⊆ U ∩ V ∧ IsCompact K' ∧
          Subsingleton ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) K')).homology k)) :
    Good N c (U ∪ V) (hU.union hV) := by
  intro k m hkm
  exact ⟨pd_union_hit hU hV hI hUU hVV hII k m hkm,
    pd_union_kill_chart hU hV hI hUU hVV hII hvan k m hkm⟩

end Work.Projective
