import Mathlib
import Submission.Work.Pi6.SQM.SIG.cupCobAux
import Submission.Work.Pi6.SQM.SIG.cup1mZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup2ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup3ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cochainDiffPb
import Submission.Work.Pi6.SQM.SIG.clsPb
import Submission.Work.Pi6.SQM.SIG.pairDeltaApply
import Submission.Work.Pi6.SQM.SIG.classZeroCoboundary
import Submission.Work.Pi6.SQM.SIG.ClsAux
import Submission.Work.Pi6.SQ.sqOps
import Submission.Work.Pi6.SQM.SIG.pbLoopMixed
import Submission.Work.Pi6.SQM.SIG.deltaMixed
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- The mod-2 cup-1 product vanishes when its **second** argument is zero (used only to kill the
cross terms in the coboundary of `ã.1 ∪₁ ã.1`). -/
private theorem cup1m_zero_right_aux {X : SSet} (n m : ℕ) (u : Cochain Work.Pi6.SQ.F2 X n) :
    Work.Pi6.SQ.cup1m X n m u (0 : Cochain Work.Pi6.SQ.F2 X m) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup1m, Work.Cohomology.genEval_cup1]
  simp [Work.Cohomology.genEval]

/-- `σ` commutes with `Sq²` from `H³` (`∪₁`) to `H²` (`∪`).  Recipe: pick `ã` (relative cocycle of
degree 3) with `relIncl(relClassOf ã) = cls x` (`existsRelCocycle`) and `s` of degree 2 with
`δs = pb (evSSet K k₀) ã.1` (`existsPrimitive`, using that `PK` is contractible); `sigma_apply`
gives `σ₂(cls x) = cls (pb loopSSet s)`, so `cls z = cls (pb loopSSet s)`.  The relative cocycle
`ã.1 ∪₁ ã.1` represents `ρ(cls (x∪₁x))` (vanishing on `{k₀}` from `hN` + `cup1mZeroLeft`, cocycle
from `h1`, class from `Work.Pi6.SQ.Bridge.sqOpsProp`), and `t := A∪₁s + s∪s` with `A := q*ã.1`
satisfies `δt = A∪₁A = q*(ã.1∪₁ã.1)` (`cupCobAux`, `hN`), so `sigma_apply` gives
`σ₄(cls (x∪₁x)) = cls (pb loopSSet t)`, and `pb loopSSet t = w∪w` with `w := pb loopSSet s`
(`hN`, `pb loopSSet A = 0` since `A` vanishes on the fibre, `loopSSet = homeoSSet ≫ inclASSet`).
Finally `cupH'_apply`. -/
theorem sigmaCup1_3 (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural)
    (K : Type) [TopologicalSpace K] (k₀ : K) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) 3)
    (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) x = 0)
    (hxx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K)
      (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX K) 3 3 x x) = 0)
    (z : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) 2)
    (hz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) z = 0)
    (hzz : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀))
      (Work.Cohomology.cup Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) z z) = 0)
    (hcls : Work.Pi6.SQM.cls z hz = Work.Pi6.SQM.SIG.sigma K k₀ 2 (Work.Pi6.SQM.cls x hx)) :
    Work.Pi6.SQM.SIG.sigma K k₀ 4
        (Work.Pi6.SQM.cls (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX K) 3 3 x x) hxx) =
      Work.Pi6.SQM.cls (Work.Cohomology.cup Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀)) z z) hzz := by
  -- 1. a relative cocycle `ã` representing `ρ(cls x)`.
  obtain ⟨ã, hã, hrel⟩ := existsRelCocycle (TopCat.of K) ({k₀} : Set K) 3
    ((rhoLM K k₀ 1).hom (cls x hx))
  -- 2. `A := q*ã.1` is a cocycle on the path space, of vanishing class (`PK` is contractible),
  -- hence a coboundary `δs = A`.
  have hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (PK K k₀))
      (pb (evSSet K k₀) ã.1) = 0 := by
    rw [cochainDiffPb, relDiffLM_zero_cochainDiff ã hã, pb_zero]
  obtain ⟨s, hs⟩ : ∃ s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (SX (PK K k₀)) 2,
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (PK K k₀)) s = pb (evSSet K k₀) ã.1 := by
    refine classZeroCoboundary (SX (PK K k₀)) 2 (pb (evSSet K k₀) ã.1) hA ?_
    haveI : ContractibleSpace (PK K k₀) := Work.StemsB.contractible_pathSpace K k₀
    have hs : Subsingleton (Coh F2 (PK K k₀) 3) :=
      subsingleton_coh_of_contractible (PK K k₀) 2
    exact @Subsingleton.elim (Coh F2 (PK K k₀) 3) hs _ _
  -- 3. `σ₂(cls x) = cls (pb loopSSet s)`, hence `cls z = cls (pb loopSSet s)`.
  have hcls1 : cls x hx = (HomologicalComplex.homologyMap
      (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 3).hom
      (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã) := by
    rw [hrel]
    exact (relIncl_rhoLM K k₀ 1 (cls x hx)).symm
  have hloop : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
      (pb (loopSSet K k₀) s) = 0 := by
    rw [cochainDiffPb, hs, pb_loop_ev_relKern k₀ ã]
  have hσ2 : sigma K k₀ 2 (cls x hx) = cls (pb (loopSSet K k₀) s) hloop :=
    sigma_apply K k₀ 1 ã hã x hx hcls1 s hs hloop
  have hz' : cls z hz = cls (pb (loopSSet K k₀) s) hloop := hcls.trans hσ2
  -- 4. the mixed cochain `t = A∪₁s + s∪s` has coboundary `q*(ã.1 ∪₁ ã.1)`.
  have hst : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (PK K k₀))
      (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2 (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s) =
      pb (evSSet K k₀) (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1) :=
    deltaMixed h1 h2 h3 hN K k₀ ã hã s hs
  -- 5. the relative cocycle `ã.1 ∪₁ ã.1` representing `ρ(cls (x ∪₁ x))`.
  have hdã : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX K) ã.1 = 0 :=
    relDiffLM_zero_cochainDiff ã hã
  have hvan : ((restr Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K)).f 5).hom
      (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1) = 0 := by
    have hpbc := pb_cup1m hN (TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K)))
      3 3 ã.1 ã.1
    rw [restr_eq_pb, hpbc, relKern_restr_eq_zero ã]
    exact cup1mZeroLeft _ 3 3 0
  have hcoc : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX K)
      (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1) = 0 := by
    have hh := h1 (SX K) 3 3 ã.1 ã.1 (by norm_num) (by norm_num)
    have hh' : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX K)
        (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1) =
        Work.Cohomology.cup Work.Pi6.SQ.F2 (SX K) ã.1 ã.1
          + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX K) ã.1 ã.1
          + Work.Pi6.SQ.cup1m (SX K) 4 3
              (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX K) ã.1) ã.1
          + Work.Pi6.SQ.cup1m (SX K) 3 4 ã.1
              (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX K) ã.1) := hh
    have key : (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX K) ã.1 ã.1
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX K) ã.1 ã.1
        + Work.Pi6.SQ.cup1m (SX K) 4 3 (0 : Cochain Work.Pi6.SQ.F2 (SX K) 4) ã.1
        + Work.Pi6.SQ.cup1m (SX K) 3 4 ã.1
            (0 : Cochain Work.Pi6.SQ.F2 (SX K) 4)) = 0 := by
      have hz1 : Work.Pi6.SQ.cup1m (SX K) 4 3
          (0 : Cochain Work.Pi6.SQ.F2 (SX K) 4) ã.1 = 0 :=
        cup1mZeroLeft (SX K) 4 3 ã.1
      have hz2 : Work.Pi6.SQ.cup1m (SX K) 3 4 ã.1
          (0 : Cochain Work.Pi6.SQ.F2 (SX K) 4) = 0 :=
        cup1m_zero_right_aux 3 4 ã.1
      rw [hz1, hz2, cochainAddSelf]
      simp
    rw [hh', hdã]
    exact key
  have hÃ : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) 5
      (⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩ :
        relKern F2 (TopCat.of K) ({k₀} : Set K) 5) = 0 := by
    apply Subtype.ext
    simp only [relDiffLM_coe, Submodule.coe_zero]
    rw [singularCochain_d_apply F2 (TopCat.of K)]
    exact hcoc
  have hclã : cls ã.1 hdã = cls x hx := by
    have h1' := Work.Cohomology.relIncl_homologyMap_relClassOf F2 (TopCat.of K)
      ({k₀} : Set K) ã hã
    rw [hrel] at h1'
    rw [relIncl_rhoLM K k₀ 1 (cls x hx)] at h1'
    have e : Work.Cohomology.cohomologyClassOf F2 (SX K) ã.1 hdã =
        Work.Cohomology.cohomologyClassOf F2 (SX K) ã.1
          (relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K) ã hã) :=
      Work.Cohomology.cohomologyClassOf_congr F2 (SX K) (rfl : ã.1 = ã.1) hdã
        (relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K) ã hã)
    exact e.trans h1'.symm
  have hclass : (HomologicalComplex.homologyMap
      (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 5).hom
      (relClassOf F2 (TopCat.of K) ({k₀} : Set K)
        (⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩ :
          relKern F2 (TopCat.of K) ({k₀} : Set K) 5) hÃ) =
      cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx := by
    rw [Work.Cohomology.relIncl_homologyMap_relClassOf F2 (TopCat.of K) ({k₀} : Set K)
      (⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩ :
        relKern F2 (TopCat.of K) ({k₀} : Set K) 5) hÃ]
    have e2 : Work.Cohomology.cohomologyClassOf F2 (SX K)
        (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1)
        (relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K)
          (⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩ :
            relKern F2 (TopCat.of K) ({k₀} : Set K) 5) hÃ) =
        cls (Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1) hcoc :=
      Work.Cohomology.cohomologyClassOf_congr F2 (SX K)
        (rfl : Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1 =
          Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1)
        (relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K)
          (⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩ :
            relKern F2 (TopCat.of K) ({k₀} : Set K) 5) hÃ) hcoc
    exact e2.trans (cls_cup1m_eq_3 ã.1 x hdã hx hcoc hxx hclã)
  obtain ⟨Ã, hÃ', hcoe, hclass'⟩ : ∃ (Ã : relKern F2 (TopCat.of K) ({k₀} : Set K) 5)
      (hÃ : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) 5 Ã = 0),
      Ã.1 = Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1 ∧
      (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) 5).hom
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) Ã hÃ) =
        cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx :=
    ⟨⟨Work.Pi6.SQ.cup1m (SX K) 3 3 ã.1 ã.1, hvan⟩, hÃ, rfl, hclass⟩
  have hst' : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (PK K k₀))
      (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2 (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s) = pb (evSSet K k₀) Ã.1 := by
    rw [hcoe]
    exact hst
  have ht : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
      (pb (loopSSet K k₀) (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2 (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s)) = 0 := by
    rw [cochainDiffPb, hst, ← hcoe, pb_loop_ev_relKern k₀ Ã]
  -- 6. `σ₄(cls (x ∪₁ x)) = cls (pb loopSSet t)`.
  have hσ4 : sigma K k₀ 4 (cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx) =
      cls (pb (loopSSet K k₀) (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2 (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s)) ht :=
    sigma_apply K k₀ 3 Ã hÃ' (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx hclass'.symm
      (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2 (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s) hst' ht
  -- 7. `pb loopSSet t = pb loopSSet s ∪ pb loopSSet s`.
  have hss : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
      (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
        (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) = 0 := by
    rw [← pbLoopMixed hN K k₀ ã s]
    exact ht
  have hzu : cls (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (Path k₀ k₀)) z z) hzz =
      cls (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
        (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) hss :=
    cls_cup_eq z (pb (loopSSet K k₀) s) hz hloop hzz hss hz'
  have hA2 : cls (pb (loopSSet K k₀) (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2
        (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s)) ht =
      cls (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
        (pb (loopSSet K k₀) s) (pb (loopSSet K k₀) s)) hss :=
    cohomologyClassOf_congr Work.Pi6.SQ.F2 (SX (Path k₀ k₀))
      (pbLoopMixed hN K k₀ ã s) ht hss
  have hA3 : cls (pb (loopSSet K k₀) (Work.Pi6.SQ.cup1m (SX (PK K k₀)) 3 2
        (pb (evSSet K k₀) ã.1) s
        + Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (PK K k₀)) s s)) ht =
      cls (Work.Cohomology.cup Work.Pi6.SQ.F2 (SX (Path k₀ k₀)) z z) hzz :=
    hA2.trans hzu.symm
  exact hσ4.trans hA3

end

end Work.Pi6.SQM.SIG
