import Mathlib
import Submission.Work.Pi6.SQM.SIG.cupCobAux
import Submission.Work.Pi6.SQM.SIG.cup1mZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup2ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup3ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cochainDiffPb
import Submission.Work.Pi6.SQM.SIG.clsPb
import Submission.Work.Pi6.SQM.SIG.pairDeltaApply
import Submission.Work.Pi6.SQM.SIG.classZeroCoboundary
import Submission.Work.Pi6.SQM.SIG.Wd3
import Submission.Work.Pi6.SQ.sqOps
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

open Work.Cohomology (Cochain genEval genEval_ext genEval_add cochainDiff cohomologyClassOf
  cochainDiff_cochainDiff relClassOf relKern relDiffLM relDiffLM_coe relIncl)

/-- The `∪₃` coboundary formula (`Cup3Cob`) at degrees `(5,5)`, in cast-free form (own copy, under a
private name, so that this file does not depend on the accident of which degree-instances of the
coboundary formulas happen to be present in the shared file `Wd3`). -/
theorem cup3CobFiveFive (h3 : Cup3Cob) (X : SSet) (u v : Cochain F2 X 5) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 5 u v) =
      Work.Pi6.SQ.cup2 X 5 5 u v + Work.Pi6.SQ.cup2 X 5 5 v u +
      Work.Pi6.SQM.cup3 X 6 5 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 5 6 u (cochainDiff F2 X v) := by
  have h := h3 X 5 5 u v (by omega) (by omega)
  simpa only [show (5:ℕ) + 1 = 6 from rfl] using h

/-- Clause (c4) of `SigmaStar`: `σ` commutes with `Sq²` from `H⁵` (`∪₃`) to `H⁴` (`∪₂`).
Recipe as for `sigmaCup2_4`; the representative-independence of the `∪₃`-square (needed because `z`
is arbitrary) follows from `h2`/`h3` as in `Pi6/SQM/SIG/cup3Wd`. -/
theorem sigmaCup3_5 (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural)
    (K : Type) [TopologicalSpace K] (k₀ : K) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) 5)
    (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) x = 0)
    (hxx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K)
      (Work.Pi6.SQM.cup3 (Work.Pi6.SQM.SX K) 5 5 x x) = 0)
    (z : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) 4)
    (hz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) z = 0)
    (hzz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup2 (Work.Pi6.SQM.SX (Path k₀ k₀)) 4 4 z z) = 0)
    (hcls : Work.Pi6.SQM.cls z hz = Work.Pi6.SQM.SIG.sigma K k₀ 4 (Work.Pi6.SQM.cls x hx)) :
    Work.Pi6.SQM.SIG.sigma K k₀ 6
        (Work.Pi6.SQM.cls (Work.Pi6.SQM.cup3 (Work.Pi6.SQM.SX K) 5 5 x x) hxx) =
      Work.Pi6.SQM.cls (Work.Pi6.SQ.cup2 (Work.Pi6.SQM.SX (Path k₀ k₀)) 4 4 z z) hzz := by
  -- (1) a relative cocycle representing `ρ(cls x)`
  obtain ⟨ã, hã, hclass⟩ := existsRelCocycle (TopCat.of K) ({k₀} : Set K) 5
    ((rhoLM K k₀ 3).hom (Work.Pi6.SQM.cls x hx))
  have hclsã : Work.Pi6.SQM.cls x hx =
      (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 5).hom
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã) := by
    rw [hclass, relIncl_rhoLM]
  have hdã : cochainDiff F2 (SX K) ã.1 = 0 := relDiffLM_zero_cochainDiff ã hã
  have hclsmem : cohomologyClassOf F2 (SX K) ã.1 hdã = Work.Pi6.SQM.cls x hx := by
    have h := relIncl_homologyMap_relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã
    rw [hclass, relIncl_rhoLM] at h
    exact h.symm
  -- (2) the primitive `s` on the contractible path space
  have hqδ : relDiffLM F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) 5 (qStarRel K k₀ 5 ã) = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero, pairMapK_coe,
      singularCochain_d_apply F2 (TopCat.of (PK K k₀)), cochainDiffPb (evSSet K k₀) 5 ã.1,
      hdã, pb_zero]
  haveI : ContractibleSpace (PK K k₀) := Work.StemsB.contractible_pathSpace K k₀
  have hvanish : cohomologyClassOf F2 (SX (PK K k₀)) (pb (evSSet K k₀) ã.1)
      (by rw [cochainDiffPb (evSSet K k₀) 5 ã.1, hdã, pb_zero]) = 0 := by
    haveI : Subsingleton ↑((SSetCochainComplex F2 (SX (PK K k₀))).homology 5) :=
      subsingleton_coh_of_contractible (PK K k₀) 4
    exact Subsingleton.elim _ _
  have hqvan : cohomologyClassOf F2 (SX (PK K k₀)) (qStarRel K k₀ 5 ã).1
      (relDiffLM_zero_cochainDiff (qStarRel K k₀ 5 ã) hqδ) = 0 :=
    (cohomologyClassOf_congr F2 (SX (PK K k₀)) (pairMapK_coe K k₀ ã) _ _).trans hvanish
  obtain ⟨s, hs⟩ := existsPrimitive (TopCat.of (PK K k₀)) (fibreSet K k₀) 4
    (qStarRel K k₀ 5 ã) hqδ hqvan
  have hsA : cochainDiff F2 (SX (PK K k₀)) s = pb (evSSet K k₀) ã.1 := by
    rw [← pairMapK_coe]; exact hs
  -- the computation rule at `n = 3`: `σ₄(cls x) = cls (pb loop s)`
  have hloopA : pb (loopSSet K k₀) (pb (evSSet K k₀) ã.1) = 0 := pb_loop_ev_relKern k₀ ã
  have hws : cochainDiff F2 (SX (Path k₀ k₀)) (pb (loopSSet K k₀) s) = 0 := by
    rw [cochainDiffPb (loopSSet K k₀) 4 s, hsA]
    exact hloopA
  have hσ4 : Work.Pi6.SQM.SIG.sigma K k₀ 4 (Work.Pi6.SQM.cls x hx) =
      Work.Pi6.SQM.cls (pb (loopSSet K k₀) s) hws :=
    sigma_apply K k₀ 3 ã hã x hx hclsã s hsA hws
  -- (3) `η := ã.1 ∪₃ ã.1` is a relative cocycle representing `ρ(cls (x ∪₃ x))`
  have hηmem : ((restr F2 (TopCat.of K) ({k₀} : Set K)).f 7).hom
      (Work.Pi6.SQM.cup3 (SX K) 5 5 ã.1 ã.1) = 0 := by
    rw [restr_eq_pb, pb_cup3 hN, relKern_restr_eq_zero ã, cup3ZeroLeft]
  let η : relKern F2 (TopCat.of K) ({k₀} : Set K) 7 :=
    ⟨Work.Pi6.SQM.cup3 (SX K) 5 5 ã.1 ã.1, by
      rw [relKern, LinearMap.mem_ker]; exact hηmem⟩
  have hηcoc : cochainDiff F2 (SX K) η.1 = 0 := by
    show cochainDiff F2 (SX K) (Work.Pi6.SQM.cup3 (SX K) 5 5 ã.1 ã.1) = 0
    rw [cup3CobFiveFive h3, hdã]
    simp only [cup3ZeroLeft, cup3_zero_right, add_zero]
    exact add_self_eq_zero_f2 _
  have hηdre : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) 7 η = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero, singularCochain_d_apply F2 (TopCat.of K) η.1]
    exact hηcoc
  have hηcls : cohomologyClassOf F2 (SX K) η.1 hηcoc =
      cohomologyClassOf F2 (SX K) (Work.Pi6.SQM.cup3 (SX K) 5 5 x x) hxx :=
    cls_cup3_eq_5 h2 h3 ã.1 x hdã hx hηcoc hxx hclsmem
  have hclsη : Work.Pi6.SQM.cls (Work.Pi6.SQM.cup3 (SX K) 5 5 x x) hxx =
      (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 7).hom
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) η hηdre) := by
    rw [relIncl_homologyMap_relClassOf]
    exact hηcls.symm
  -- (4) the primitive `t` on the path space, and its restriction to the loops
  set A : Cochain F2 (SX (PK K k₀)) 5 := pb (evSSet K k₀) ã.1 with hAdef
  have hAδ : cochainDiff F2 (SX (PK K k₀)) A = 0 := by
    rw [hAdef, cochainDiffPb (evSSet K k₀) 5 ã.1, hdã, pb_zero]
  have hsA' : cochainDiff F2 (SX (PK K k₀)) s = A := by rw [hAdef]; exact hsA
  set t : Cochain F2 (SX (PK K k₀)) 6 :=
    Work.Pi6.SQM.cup3 (SX (PK K k₀)) 5 4 A s
      + Work.Pi6.SQ.cup2 (SX (PK K k₀)) 4 4 s s with ht
  have htδ : cochainDiff F2 (SX (PK K k₀)) t = pb (evSSet K k₀) η.1 := by
    have hcob := (cupCobAux h1 h2 h3).2.2.2.2 (SX (PK K k₀)) A s hAδ hsA'
    rw [ht, hcob, hAdef]
    rw [← pb_cup3 hN (evSSet K k₀) 5 5 ã.1 ã.1]
  have hloopA' : pb (loopSSet K k₀) A = 0 := by rw [hAdef]; exact hloopA
  have htrel : pb (loopSSet K k₀) t = Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
      (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s) := by
    rw [ht, pb_add, pb_cup3 hN (loopSSet K k₀) 5 4 A s, pb_cup2 hN (loopSSet K k₀) 4 4 s s,
      hloopA', cup3ZeroLeft, zero_add]
  have hww : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
      (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) = 0 := by
    rw [cup2Cob44 h2 (SX (Path k₀ k₀)) (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s), hws]
    simp only [cup2ZeroLeft, cup2_zero_right, add_zero]
    exact add_self_eq_zero_f2 _
  -- (5) `σ₆(cls (x ∪₃ x)) = cls (pb loop t)`
  have hσ6 : Work.Pi6.SQM.SIG.sigma K k₀ 6
      (Work.Pi6.SQM.cls (Work.Pi6.SQM.cup3 (SX K) 5 5 x x) hxx) =
      Work.Pi6.SQM.cls (pb (loopSSet K k₀) t) (by rw [htrel]; exact hww) :=
    sigma_apply K k₀ 5 η hηdre (Work.Pi6.SQM.cup3 (SX K) 5 5 x x) hxx hclsη t htδ
      (by rw [htrel]; exact hww)
  -- (6) conclude
  have hwz : Work.Pi6.SQM.cls (pb (loopSSet K k₀) s) hws = Work.Pi6.SQM.cls z hz := by
    rw [hσ4] at hcls
    exact hcls.symm
  have hfinal : Work.Pi6.SQM.cls (pb (loopSSet K k₀) t) (by rw [htrel]; exact hww) =
      Work.Pi6.SQM.cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
        (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) hww :=
    cohomologyClassOf_congr F2 (SX (Path k₀ k₀)) htrel _ hww
  rw [hσ6, hfinal]
  exact cls_cup2_eq_4 (u := pb (loopSSet K k₀) s) (v := z) hws hz hww hzz hwz

end

end Work.Pi6.SQM.SIG
