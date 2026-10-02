import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.tcmPhiAux
import Submission.Work.Whitney.tcmF_inv_general
import Submission.Work.Whitney.CutoffClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The rank-one model product formula: the spherical form and the final assembly

This module isolates the **sphere-group form** of the rank-one case of the model product formula,

  `tcmRankOneLHS Y n = (-1)^n • Mn (n+1) Y`   in `H^{n+1}(Y × ℝ^{n+1}, Sph Y (n+1))`,

and proves that it implies the target `Work.Whitney.rankOne_cup_model` (the assembly is
`Work.Whitney.tcmProd_eq_of_tcmRankOneLHS`, which is pure `jMap`-bookkeeping plus `Mpun_spec`).

The slogan: the target lives in the **punctured** group; applying the pair inclusion
`jMap : H^{n+1}(X, Punct) → H^{n+1}(X, Sph)` (an isomorphism, `Work.Thom.bijective_jMap`) turns the
left hand side into the `Φ`-transport of the relative–relative cup and the right hand side into
`Mn (n+1)`.  See `rankOne_cup_model_NOTES.md` §26.
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

/-- **The left hand side of the rank-one model formula, transported into the sphere group**: the
relative–relative cup of the two pulled-back model classes, moved along the inverse coordinate
identification `Fib.tcmF_inv` into `H^{n+1}(Y × ℝ^{n+1}, Sph Y (n+1))`. -/
def tcmRankOneLHS (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    RelCoh ℤ (n + 1) (Y × EuclideanSpace ℝ (Fin (n + 1))) (Sph Y (n + 1)) :=
  (relCohMap (Fib.tcmF_inv Y n 1) (Sph Y (n + 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
    (tcmF_inv_mem' (Y := Y) n 1) ℤ (n + 1)).hom
    (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
      ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
      ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y)))

/-- **Bookkeeping**: the pair inclusion `jMap : H^{n+1}(X,Punct) → H^{n+1}(X,Sph)` sends the left
hand side of the target to `tcmRankOneLHS Y n`. -/
theorem jMap_tcmProd (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (n + 1)))) (Sph Y (n + 1))
        (Punct Y (n + 1)) (mem_Sph_punct Y (n + 1)) ℤ (n + 1)).hom
      (tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y))
    = tcmRankOneLHS Y n := by
  rw [tcmProd, tcmRankOneLHS]
  rw [relCohMap_compA_apply (Sph Y (n + 1)) (Punct Y (n + 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
    (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (n + 1)))) (Fib.tcmF_inv Y n 1)
    (mem_Sph_punct Y (n + 1)) (tcmF_inv_mem_punct_union Y n 1)
    (fun y hy => tcmF_inv_mem_punct_union Y n 1 y (mem_Sph_punct Y (n + 1) y hy)) ℤ (n + 1) _]
  congr 1

/-- **The assembly**: the spherical form of the rank-one model product formula implies the target
`Work.Whitney.rankOne_cup_model` at degree `n` (nonempty or not). -/
theorem tcmProd_eq_of_tcmRankOneLHS (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (n : ℕ)
    (h : tcmRankOneLHS Y n = ((-1 : ℤ) ^ n) • (Mn (n + 1) Y)) :
    tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y) = ((-1 : ℤ) ^ n) • (Mpun (n + 1) Y) := by
  apply (bijective_jMap Y (n + 1) (n + 1)).1
  rw [jMap_tcmProd, h, map_zsmul, Mpun_spec]

end

end Work.Whitney
