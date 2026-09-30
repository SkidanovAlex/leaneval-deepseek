import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.CapGeomDefs
import Submission.Work.Thom.CapChainA
import Submission.Work.Thom.ATools

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

namespace Work.Thom

namespace CleanA

open CategoryTheory

noncomputable section

/-- The pair condition of the cap map of the statement: it carries the boundary sphere into the
lower band (`mLower n = sphLe n (1/2)` definitionally). -/
theorem capMapPairSph_mem (B : Type) [TopologicalSpace B] (n : ℕ) :
    ∀ q ∈ Abound B n, capMapPairSph B n q ∈ ppLe B n := by
  intro q hq
  have hlast : lastC n (capMap n q.2.1) = 0 := by
    rw [lastC, capMap_last, show ‖q.2.1‖ = 1 from hq]
    norm_num
  refine ⟨(capMapPairSph B n q).2.2, ?_⟩
  show lastC n (capMap n q.2.1) ≤ 1 / 2
  rw [hlast]
  norm_num

/-- **The cap map induces an isomorphism of relative cohomology.**  The map of pairs `(b, w) ↦ (b, (w, √(1 - ‖w‖²)))` from `(B × ball n, B × sph n)` to the sphere-bundle pair `(B × sph (n+1), B × lower n)` induces a bijection on relative cohomology in every degree.  This is the identification of the Thom pair of rank `n` with the sphere-bundle pair of rank `n+1` over the lower region, i.e. the suspension step of the induction. -/
theorem capRelCohIso (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((relCohMap (capMapPairSph B n)
        ({q : B × MBall n | q.2.1 ∈ mSph n})
        ({p : B × MSph (n + 1) | p.2.1 ∈ mLower n})
        (fun q hq => by
          have h1 : capMap n (q.2 : EuclideanSpace ℝ (Fin n)) ∈ mLower n :=
            equator_subset_mLower n (capMap_mem_equator n hq)
          simpa [capMapPairSph] using h1) ℤ m).hom) := by
  classical
  -- the three steps are isomorphisms
  haveI hb : CategoryTheory.IsIso (relCohMap (ContinuousMap.id (B × MSph (n + 1)))
      (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) ℤ m) :=
    isIso_relCohMap_bandIncl B n m
  haveI he : CategoryTheory.IsIso (relCohMap (excMap B n) (Qset B n) (ppLt B n)
      (excMap_mem B n) ℤ m) :=
    isIso_relCohMap_excision B n m
  haveI hc : CategoryTheory.IsIso (relCohMap (capMapPairC B n) (Abound B n) (Qset B n)
      (capQ_mem B n) ℤ m) :=
    isIso_relCohMap_cap B n m
  -- the composite of the three pullbacks
  have hiso : CategoryTheory.IsIso ((relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) ℤ m) ≫ (relCohMap (excMap B n) (Qset B n) (ppLt B n) (excMap_mem B n) ℤ m) ≫ (relCohMap (capMapPairC B n) (Abound B n) (Qset B n) (capQ_mem B n) ℤ m)) :=
    inferInstance
  -- functoriality: the composite is a single pullback
  have hcomp1 := relCohMap_compA (A := Abound B n) (B := Qset B n) (C := ppLt B n)
    (f := capMapPairC B n) (g := excMap B n) (capQ_mem B n) (excMap_mem B n)
    (fun q hq => excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq)) ℤ m
  have hcomp2 := relCohMap_compA (A := Abound B n) (B := ppLt B n) (C := ppLe B n)
    (f := (excMap B n).comp (capMapPairC B n)) (g := ContinuousMap.id (B × MSph (n + 1)))
    (fun q hq => excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))
    (fun x hx => ppLt_subset_ppLe B n hx)
    (fun q hq => ppLt_subset_ppLe B n
      (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) ℤ m
  -- the composite is an isomorphism
  have hsingle : ((relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) ℤ m) ≫ (relCohMap (excMap B n) (Qset B n) (ppLt B n) (excMap_mem B n) ℤ m) ≫ (relCohMap (capMapPairC B n) (Abound B n) (Qset B n) (capQ_mem B n) ℤ m))
      = relCohMap ((ContinuousMap.id (B × MSph (n + 1))).comp
          ((excMap B n).comp (capMapPairC B n))) (Abound B n) (ppLe B n)
          (fun q hq => ppLt_subset_ppLe B n
            (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) ℤ m :=
    (congrArg (fun z =>
        (relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
          (fun x hx => ppLt_subset_ppLe B n hx) ℤ m) ≫ z) hcomp1).trans hcomp2
  -- the composite map of pairs is the cap map of the statement
  have hmap : (ContinuousMap.id (B × MSph (n + 1))).comp ((excMap B n).comp (capMapPairC B n))
      = capMapPairSph B n := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  have hcongr : relCohMap ((ContinuousMap.id (B × MSph (n + 1))).comp
        ((excMap B n).comp (capMapPairC B n))) (Abound B n) (ppLe B n)
        (fun q hq => ppLt_subset_ppLe B n
          (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) ℤ m
      = relCohMap (capMapPairSph B n) (Abound B n) (ppLe B n) (capMapPairSph_mem B n) ℤ m :=
    relCohMap_congrA (Abound B n) (ppLe B n) hmap
      (fun q hq => ppLt_subset_ppLe B n
        (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq)))
      (capMapPairSph_mem B n) ℤ m
  -- the statement's map is the cap map of the chain
  haveI hfinal : CategoryTheory.IsIso (relCohMap (capMapPairSph B n) (Abound B n) (ppLe B n)
      (capMapPairSph_mem B n) ℤ m) :=
    hcongr ▸ hsingle ▸ hiso
  -- the pairs of the statement are definitionally those of the chain
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hfinal

end

end CleanA

end Work.Thom
