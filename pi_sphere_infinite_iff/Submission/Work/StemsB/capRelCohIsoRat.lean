import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.capRelCohIso
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.StemsB.SuspensionStepR
import Submission.Work.StemsB.CapChainR

set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

namespace Work.StemsB

open CategoryTheory
open Work.Thom

theorem capRelCohIsoRat (R : Type) [CommRing R] (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((Work.Thom.relCohMap (Work.Thom.capMapPairSph B n)
        ({q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n})
        ({p : B × Work.Thom.MSph (n + 1) | p.2.1 ∈ Work.Thom.mLower n})
        (fun q hq => by
          have h1 : Work.Thom.capMap n (q.2 : EuclideanSpace ℝ (Fin n)) ∈ Work.Thom.mLower n :=
            Work.Thom.equator_subset_mLower n (Work.Thom.capMap_mem_equator n hq)
          simpa [Work.Thom.capMapPairSph] using h1) R m).hom) := by
  classical
  -- the three steps are isomorphisms
  haveI hb : CategoryTheory.IsIso (relCohMap (ContinuousMap.id (B × MSph (n + 1)))
      (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) R m) :=
    isIso_relCohMap_bandIncl_R R B n m
  haveI he : CategoryTheory.IsIso (relCohMap (excMap B n) (Qset B n) (ppLt B n)
      (excMap_mem B n) R m) :=
    isIso_relCohMap_excision_R R B n m
  haveI hc : CategoryTheory.IsIso (relCohMap (capMapPairC B n) (Abound B n) (Qset B n)
      (capQ_mem B n) R m) :=
    isIso_relCohMap_cap_R R B n m
  -- the composite of the three pullbacks
  have hiso : CategoryTheory.IsIso ((relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) R m) ≫ (relCohMap (excMap B n) (Qset B n) (ppLt B n) (excMap_mem B n) R m) ≫ (relCohMap (capMapPairC B n) (Abound B n) (Qset B n) (capQ_mem B n) R m)) :=
    inferInstance
  -- functoriality: the composite is a single pullback
  have hcomp1 := relCohMap_comp' (A := Abound B n) (B := Qset B n) (C := ppLt B n)
    (f := capMapPairC B n) (g := excMap B n) (capQ_mem B n) (excMap_mem B n)
    (fun q hq => excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq)) R m
  have hcomp2 := relCohMap_comp' (A := Abound B n) (B := ppLt B n) (C := ppLe B n)
    (f := (excMap B n).comp (capMapPairC B n)) (g := ContinuousMap.id (B × MSph (n + 1)))
    (fun q hq => excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))
    (fun x hx => ppLt_subset_ppLe B n hx)
    (fun q hq => ppLt_subset_ppLe B n
      (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) R m
  -- the composite is an isomorphism
  have hsingle : ((relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n) (fun x hx => ppLt_subset_ppLe B n hx) R m) ≫ (relCohMap (excMap B n) (Qset B n) (ppLt B n) (excMap_mem B n) R m) ≫ (relCohMap (capMapPairC B n) (Abound B n) (Qset B n) (capQ_mem B n) R m))
      = relCohMap ((ContinuousMap.id (B × MSph (n + 1))).comp
          ((excMap B n).comp (capMapPairC B n))) (Abound B n) (ppLe B n)
          (fun q hq => ppLt_subset_ppLe B n
            (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) R m :=
    (congrArg (fun z =>
        (relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
          (fun x hx => ppLt_subset_ppLe B n hx) R m) ≫ z) hcomp1).trans hcomp2
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
          (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq))) R m
      = relCohMap (capMapPairSph B n) (Abound B n) (ppLe B n) (capMapPairSph_mem B n) R m :=
    relCohMap_congr' (Abound B n) (ppLe B n) hmap
      (fun q hq => ppLt_subset_ppLe B n
        (excMap_mem B n (capMapPairC B n q) (capQ_mem B n q hq)))
      (capMapPairSph_mem B n) R m
  -- the statement's map is the cap map of the chain
  haveI hfinal : CategoryTheory.IsIso (relCohMap (capMapPairSph B n) (Abound B n) (ppLe B n)
      (capMapPairSph_mem B n) R m) :=
    hcongr ▸ hsingle ▸ hiso
  -- the pairs of the statement are definitionally those of the chain
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hfinal

end Work.StemsB
