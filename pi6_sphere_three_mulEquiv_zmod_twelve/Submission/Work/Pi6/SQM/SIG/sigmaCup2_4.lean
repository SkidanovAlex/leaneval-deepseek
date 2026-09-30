import Mathlib
import Submission.Work.Pi6.SQM.SIG.cupCobAux
import Submission.Work.Pi6.SQM.SIG.cup1mZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup2ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup3ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cochainDiffPb
import Submission.Work.Pi6.SQM.SIG.clsPb
import Submission.Work.Pi6.SQM.SIG.pairDeltaApply
import Submission.Work.Pi6.SQM.SIG.classZeroCoboundary
import Submission.Work.Pi6.SQ.sqOps
import Submission.Work.Pi6.SQM.SIG.Wd3
import Submission.Work.Pi6.SQM.SIG.ClsAux
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
  cochainDiff_cochainDiff relClassOf relKern relDiffLM relDiffLM_coe relIncl
  cohomologyClassOf_congr)

/-- The `∪₁` coboundary formula at the single pair of degrees `(3,3)`, written without the degree
casts of `Cup1Cob`. -/
theorem cup1CobFormula33 (h1 : Work.Pi6.SQM.Cup1Cob) (X : SSet)
    (u v : Cochain F2 X 3) :
    cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 3 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u +
      Work.Pi6.SQ.cup1m X 4 3 (cochainDiff F2 X u) v +
      Work.Pi6.SQ.cup1m X 3 4 u (cochainDiff F2 X v) := by
  have h := h1 X 3 3 u v (by omega) (by omega)
  simpa only [show (3 : ℕ) + 1 = 4 from rfl] using h

/-- Clause (c5) of `SigmaStar`: `σ` commutes with `Sq²` from `H⁴` (`∪₂`) to `H³` (`∪₁`).
Recipe: `Work.Pi6.SQM.SIG.sigma_apply` + `Work.Pi6.SQM.SIG.existsRelCocycle` +
`Work.Pi6.SQM.SIG.existsPrimitive` + `cupCobAux` + `hN`.  Representative-independence of the
`∪₁`/`∪₂`-squares (needed because `z` is an arbitrary representative) follows from `h1`/`h2`
directly; alternatively `Work.Pi6.SQ.sqOpsProp` (in `Pi6/SQ/Bridge`, if that module is importable)
provides those clauses. -/
theorem sigmaCup2_4 (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural)
    (K : Type) [TopologicalSpace K] (k₀ : K) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) 4)
    (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) x = 0)
    (hxx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K)
      (Work.Pi6.SQ.cup2 (Work.Pi6.SQM.SX K) 4 4 x x) = 0)
    (z : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) 3)
    (hz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) z = 0)
    (hzz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX (Path k₀ k₀)) 3 3 z z) = 0)
    (hcls : Work.Pi6.SQM.cls z hz = Work.Pi6.SQM.SIG.sigma K k₀ 3 (Work.Pi6.SQM.cls x hx)) :
    Work.Pi6.SQM.SIG.sigma K k₀ 5
        (Work.Pi6.SQM.cls (Work.Pi6.SQ.cup2 (Work.Pi6.SQM.SX K) 4 4 x x) hxx) =
      Work.Pi6.SQM.cls (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX (Path k₀ k₀)) 3 3 z z) hzz := by
  -- (1) a relative cocycle `ã` of degree `4` representing `ρ(cls x)`
  obtain ⟨ã, hã, hclass⟩ := existsRelCocycle (TopCat.of K) ({k₀} : Set K) 4
    ((rhoLM K k₀ 2).hom (Work.Pi6.SQM.cls x hx))
  have hdã : cochainDiff F2 (SX K) ã.1 = 0 :=
    relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K) ã hã
  have hclsã : Work.Pi6.SQM.cls x hx =
      HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 4
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã) := by
    rw [← relIncl_rhoLM K k₀ 2 (Work.Pi6.SQM.cls x hx), hclass]
  have hclsmem : cohomologyClassOf F2 (SX K) ã.1 hdã = Work.Pi6.SQM.cls x hx := by
    have h := relIncl_homologyMap_relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã
    rw [hclass] at h
    rw [relIncl_rhoLM] at h
    exact h.symm
  -- (2) the primitive `s` on the contractible path space
  have hqδ : relDiffLM F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) 4 (qStarRel K k₀ 4 ã) = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero, pairMapK_coe, singularCochain_d_apply,
      cochainDiffPb (evSSet K k₀) 4 ã.1, hdã, pb_zero]
  haveI : ContractibleSpace (PK K k₀) := Work.StemsB.contractible_pathSpace K k₀
  have hvanish : cohomologyClassOf F2 (SX (PK K k₀)) (qStarRel K k₀ 4 ã).1
      (relDiffLM_zero_cochainDiff (qStarRel K k₀ 4 ã) hqδ) = 0 := by
    haveI : Subsingleton (Coh F2 (PK K k₀) 4) :=
      subsingleton_coh_of_contractible (PK K k₀) 3
    exact Subsingleton.elim (α := Coh F2 (PK K k₀) 4) _ _
  obtain ⟨s, hs⟩ := existsPrimitive (TopCat.of (PK K k₀)) (fibreSet K k₀) 3
    (qStarRel K k₀ 4 ã) hqδ hvanish
  have hsA : cochainDiff F2 (SX (PK K k₀)) s = pb (evSSet K k₀) ã.1 := by
    rw [← pairMapK_coe]; exact hs
  have hloopA : pb (loopSSet K k₀) (pb (evSSet K k₀) ã.1) = 0 := pb_loop_ev_relKern k₀ ã
  have hws : cochainDiff F2 (SX (Path k₀ k₀)) (pb (loopSSet K k₀) s) = 0 := by
    rw [cochainDiffPb (loopSSet K k₀) 3 s, hsA, hloopA]
  have hσ3 : Work.Pi6.SQM.SIG.sigma K k₀ 3 (Work.Pi6.SQM.cls x hx) =
      Work.Pi6.SQM.cls (pb (loopSSet K k₀) s) hws :=
    sigma_apply K k₀ 2 ã hã x hx hclsã s hsA hws
  -- (3) `η := ã.1 ∪₂ ã.1` is a relative cocycle representing `ρ(cls (x ∪₂ x))`
  have hηmem : ((restr F2 (TopCat.of K) ({k₀} : Set K)).f 6).hom
      (Work.Pi6.SQ.cup2 (SX K) 4 4 ã.1 ã.1) = 0 := by
    rw [restr_eq_pb, pb_cup2 hN, relKern_restr_eq_zero ã, cup2ZeroLeft]
  let η : relKern F2 (TopCat.of K) ({k₀} : Set K) 6 :=
    ⟨Work.Pi6.SQ.cup2 (SX K) 4 4 ã.1 ã.1, by
      rw [relKern, LinearMap.mem_ker]
      exact hηmem⟩
  have hηcoc : cochainDiff F2 (SX K) η.1 = 0 := by
    show cochainDiff F2 (SX K) (Work.Pi6.SQ.cup2 (SX K) 4 4 ã.1 ã.1) = 0
    rw [cup2Cob44 h2 (SX K) ã.1 ã.1, hdã]
    simp only [cup2_zero_left, cup2_zero_right, add_zero]
    exact add_self_eq_zero_f2 _
  have hηdre : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) 6 η = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero]
    exact hηcoc
  have hηcls : cohomologyClassOf F2 (SX K) η.1 hηcoc =
      cohomologyClassOf F2 (SX K) (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) hxx :=
    cls_cup2_eq_4 ã.1 x hdã hx hηcoc hxx hclsmem
  have hclsη : Work.Pi6.SQM.cls (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) hxx =
      HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 6
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) η hηdre) := by
    rw [relIncl_homologyMap_relClassOf]
    exact hηcls.symm
  -- (4) the primitive `t` on the path space, and its restriction to the loops
  set A : Cochain F2 (SX (PK K k₀)) 4 := pb (evSSet K k₀) ã.1 with hAdef
  have hAδ : cochainDiff F2 (SX (PK K k₀)) A = 0 := by
    rw [hAdef, cochainDiffPb (evSSet K k₀) 4 ã.1, hdã, pb_zero]
  have hsA' : cochainDiff F2 (SX (PK K k₀)) s = A := by rw [hAdef]; exact hsA
  set t : Cochain F2 (SX (PK K k₀)) 5 :=
    Work.Pi6.SQ.cup2 (SX (PK K k₀)) 4 3 A s
      + Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 3 s s with ht
  have htδ : cochainDiff F2 (SX (PK K k₀)) t = pb (evSSet K k₀) η.1 := by
    have hcob := (cupCobAux h1 h2 h3).2.2.1 (SX (PK K k₀)) A s hAδ hsA'
    rw [ht, hcob, hAdef, ← pb_cup2 hN (evSSet K k₀) 4 4 ã.1 ã.1]
  have hloopA' : pb (loopSSet K k₀) A = 0 := by rw [hAdef]; exact hloopA
  have htrel : pb (loopSSet K k₀) t =
      Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 3 3 (pb (loopSSet K k₀) s)
        (pb (loopSSet K k₀) s) := by
    rw [ht, pb_add, pb_cup2 hN (loopSSet K k₀) 4 3 A s,
      pb_cup1m hN (loopSSet K k₀) 3 3 s s, hloopA', cup2ZeroLeft, zero_add]
  have hww : cochainDiff F2 (SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 3 3 (pb (loopSSet K k₀) s)
        (pb (loopSSet K k₀) s)) = 0 := by
    rw [cup1CobFormula33 h1, hws]
    simp only [cup1mZeroLeft, cup1m_zero_right, add_zero]
    exact add_self_eq_zero_f2 _
  -- (5) `σ₅(cls (x ∪₂ x)) = cls (pb loop t)`
  have htcoc : cochainDiff F2 (SX (Path k₀ k₀)) (pb (loopSSet K k₀) t) = 0 := by
    rw [htrel]; exact hww
  have hσ5 : Work.Pi6.SQM.SIG.sigma K k₀ 5
      (Work.Pi6.SQM.cls (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) hxx) =
      Work.Pi6.SQM.cls (pb (loopSSet K k₀) t) htcoc :=
    sigma_apply K k₀ 4 η hηdre (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) hxx hclsη t htδ htcoc
  have hwz : Work.Pi6.SQM.cls (pb (loopSSet K k₀) s) hws = Work.Pi6.SQM.cls z hz := by
    rw [hσ3] at hcls
    exact hcls.symm
  have hfinal : Work.Pi6.SQM.cls (pb (loopSSet K k₀) t) htcoc =
      Work.Pi6.SQM.cls (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 3 3
        (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) hww :=
    cohomologyClassOf_congr F2 (SX (Path k₀ k₀)) htrel htcoc hww
  rw [hσ5, hfinal]
  exact cls_cup1m_eq_3 (pb (loopSSet K k₀) s) z hws hz hww hzz hwz

end

end Work.Pi6.SQM.SIG
