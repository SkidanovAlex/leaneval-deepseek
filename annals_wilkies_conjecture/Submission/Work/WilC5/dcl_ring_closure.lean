/-
  WilC5 — `dcl_ring_closure`.

  This statement used to be a hole here; it is proved as `Work.WilC5.dclClosure_ring` in
  `Submission/Work/WilC5/model_TR_of_dcl_closed.lean` and is re-exported here under the name it was
  recorded with.
-/
import Submission.Work.WilC5.model_TR_of_dcl_closed

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- A set of parameters closed under definable closure in an `LRc`-structure is closed under the
ring operations `0`, `1`, `-`, `+` and under division by `2`. -/
theorem dcl_ring_closure {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {A : Set M} (hA : Work.WilC2.Dcl A ⊆ A) :
    (0 : M) ∈ A ∧ (1 : M) ∈ A ∧ (∀ x ∈ A, -x ∈ A) ∧
      (∀ x ∈ A, x / 2 ∈ A) ∧ (∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) :=
  dclClosure_ring hA

end Work.WilC5
