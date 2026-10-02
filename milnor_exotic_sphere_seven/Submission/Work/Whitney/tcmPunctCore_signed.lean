import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.rankOne_crux
import Submission.Work.Whitney.tcmProd_rankOne_zero
import Submission.Work.Whitney.tcmModelMul_of_point
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.ATools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The rank-one case of the model product formula (the `tcmPunctCore_signed` form)

This module provides the theorem `Work.Whitney.tcmPunctCore_signed`, the rank-one case of the
external product of the model Thom classes over a base of one point,

  `tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y) = (-1)^(n·1) • Mpun (n+1) Y`,

in the form used by `Work.Whitney.tcmCup_step` (whose `tcmJ_one` is its immediate consequence).
It is proved from the crux `Work.Whitney.rankOne_crux` (`rankOne_crux.lean`, the `tcmF`-form of the
same statement) and the `n = 0` case `Work.Whitney.tcmProd_rankOne_zero`, together with the
transport identity `Work.Whitney.tcmF_tcmF_inv_transport` (pulling a class back along `tcmF` and
then along the coordinate identification `Fib.tcmF_inv` is the identity).
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- **The transport identity**: the pullback along `tcmF` followed by the pullback along the
coordinate identification `Fib.tcmF_inv` is the identity on `H^{p+q}(Y × ℝ^{p+q}, punctured)`. -/
theorem tcmF_tcmF_inv_transport_gen (Y : Type) [TopologicalSpace Y] (p q : ℕ)
    (z : RelCoh ℤ (p + q) (Y × EuclideanSpace ℝ (Fin (p + q))) (Punct Y (p + q))) :
    (relCohMap (Fib.tcmF_inv Y p q)
        (Punct Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
        (tcmF_inv_mem_punct_union Y p q) ℤ (p + q)).hom
      ((relCohMap (tcmF Y p q)
        (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
        (tcmF_mem Y p q) ℤ (p + q)).hom z) = z := by
  have hcomp : (tcmF Y p q).comp (Fib.tcmF_inv Y p q)
      = ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q))) :=
    ContinuousMap.ext (fun y => Fib.tcmF_tcmF_inv Y p q y)
  have hgf : ∀ x ∈ Punct Y (p + q),
      ((tcmF Y p q).comp (Fib.tcmF_inv Y p q)) x ∈ Punct Y (p + q) :=
    fun x hx => by
      simpa only [ContinuousMap.comp_apply, Fib.tcmF_tcmF_inv Y p q x] using hx
  rw [relCohMap_compA_apply (Punct Y (p + q)) (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
    (Fib.tcmF_inv Y p q) (tcmF Y p q) (tcmF_inv_mem_punct_union Y p q) (tcmF_mem Y p q) hgf
    ℤ (p + q) z]
  have hmap : relCohMap ((tcmF Y p q).comp (Fib.tcmF_inv Y p q))
        (Punct Y (p + q)) (Punct Y (p + q)) hgf ℤ (p + q)
      = relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q))))
          (Punct Y (p + q)) (Punct Y (p + q)) (fun x hx => hx) ℤ (p + q) :=
    relCohMap_congrA (Punct Y (p + q)) (Punct Y (p + q)) hcomp hgf (fun x hx => hx) ℤ (p + q)
  rw [hmap, relCohMap_idA (Punct Y (p + q)) ℤ (p + q)]
  rfl

/-- **The transport identity in the `q = 1` case**, the form in which it is consumed by
`Work.Whitney.tcmRankOneLHS_eq_Mn`, `Work.Whitney.rankOne_cup_model` and
`Work.Whitney.tcmProd_rankOne_signed`. -/
theorem tcmF_tcmF_inv_transport (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (z : RelCoh ℤ (p + 1) (Y × EuclideanSpace ℝ (Fin (p + 1))) (Punct Y (p + 1))) :
    (relCohMap (Fib.tcmF_inv Y p 1)
        (Punct Y (p + 1)) (tcmA Y p 1 ∪ tcmC Y p 1)
        (tcmF_inv_mem_punct_union Y p 1) ℤ (p + 1)).hom
      ((relCohMap (tcmF Y p 1)
        (tcmA Y p 1 ∪ tcmC Y p 1) (Punct Y (p + 1))
        (tcmF_mem Y p 1) ℤ (p + 1)).hom z) = z :=
  tcmF_tcmF_inv_transport_gen Y p 1 z

/-- **The rank-one case of the model product formula**, in the `tcmProd` form used by
`Work.Whitney.tcmCup_step`: `tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y) = (-1)^(n·1) • Mpun (n+1) Y`. -/
theorem tcmPunctCore_signed (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (n : ℕ) :
    tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y) = ((-1 : ℤ) ^ (n * 1)) • Mpun (n + 1) Y := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simpa using tcmProd_rankOne_zero Y
  · have hc := rankOne_crux Y n h
    rw [show tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y)
        = (relCohMap (Fib.tcmF_inv Y n 1) (Punct Y (n + 1))
            (tcmA Y n 1 ∪ tcmC Y n 1) (tcmF_inv_mem_punct_union Y n 1) ℤ (n + 1)).hom
          (tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
            ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n)
              (fun x hx => hx) ℤ n).hom (Mpun n Y))
            ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1)
              (fun x hx => hx) ℤ 1).hom (Mpun 1 Y))) from rfl]
    rw [hc, map_zsmul, tcmF_tcmF_inv_transport_gen, Nat.mul_one]

end

end Work.Whitney
