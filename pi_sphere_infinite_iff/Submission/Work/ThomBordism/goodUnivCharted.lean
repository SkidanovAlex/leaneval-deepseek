import Mathlib
import Submission.Work.ThomBordism.Port.PdGoodUnivChart
import Submission.Work.ThomBordism.Port.Glue
import Submission.Work.Cohomology.good_empty

set_option synthInstance.maxHeartbeats 400000

/-!
# Closed Poincaré duality for a compact charted space, inside the interface's import island

`Work.Cohomology.pd_good_univ_chart'` (`Port/PdGoodUnivChart.lean`) is the assembly of the `Good`
predicate for a compact `T2` space charted over `ℝ^N`, from

* the *local generation* hypothesis `hc` at the fundamental class `c ∈ H_N`, and
* the two inputs of the gluing induction: the gluing step (`Port/Glue.lean`) and `Good ∅`
  (`Work.Cohomology.good_empty`).

Both inputs are proved in the workspace, so this file records the *final* form: for every compact
`T2` space charted over `ℝ^N` with a locally generating class, **`Good N c Set.univ`**.  This is
Poincaré duality for the whole space, and it is the form consumed by
`Work.Cohomology.pd_middleDegree_of_good` (bijectivity of the middle cap product) and hence by
`Work.ThomBordism.nondegenerate_midForm_of_good` and by the finiteness of the middle cohomology of a
`Man8` (`Work.ThomBordism.goodUniv_of_localGen` below).  It lives *inside* the interface's module
island: the gluing step is the clash-free `Port/Glue.lean`, not `Work.Cohomology.pd_good_union`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-- **Poincaré duality (`Good`) for a compact charted space**, from local generation of the
fundamental class.  All the gluing technology is supplied by the ported, clash-free chain
(`Port/PdGoodUnivChart.lean`, `Port/Glue.lean`) and `Work.Cohomology.good_empty`. -/
theorem goodUniv_of_localGen {N : ℕ} {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) :
    Work.Cohomology.Good N c (Set.univ : Set M) isOpen_univ :=
  Work.Cohomology.pd_good_univ_chart' c hc hN
    (fun {_U _V} hU hV hI cc hsrc hUU hVV hII =>
      Work.Cohomology.glue_of_chart hU hV hI cc hsrc hUU hVV hII)
    (Work.Cohomology.good_empty N c)

end

end Work.ThomBordism
