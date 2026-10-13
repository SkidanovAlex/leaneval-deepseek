/-
  WilC5 — helper facts used by the maximality step of §4 (`StepKeyOfValProp.lean`).

  The two lemmas below are the ones the (now superseded) `StepKey` development supplied:
  `0` lies in every `LRc`-substructure (it is the value of a constant symbol), and `SameArch 0 0`
  holds (`SameArch x y` is `∃ N, |x| ≤ (N+1)|y| ∧ |y| ≤ (N+1)|x|`).
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.Bridge

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **`0` lies in every `LRc`-substructure**: it is the value of the `LRc`-constant for `0`. -/
theorem mem_B_zero {K : Type} [LEc.Structure K] [Field K] [Ring.CompatibleRing K]
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (B : LRc.Substructure K) : (Work.WilC5.zeroE : K) ∈ (B : Set K) :=
  B.2 (n := 0) (Sum.inl (Sum.inl Ring.zeroFunc)) (default : Fin 0 → K) (fun i => i.elim0)

/-- **`SameArch 0 0`.** -/
theorem sameArch_zero_zero {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Work.WilC5.SameArch (0 : K) 0 := ⟨0, by simp⟩

end Work.WilC5
