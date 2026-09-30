/-
# `BridgeSquare/PlanePush.lean` — pushing affine chains of `E3 = ℝ³` into a space

The pushforward of a finite affine chain (`PlaneAff.lean`) along a continuous map `G : E3 → X` is
the `ℤ`-linear extension of the affine simplexes `esimp p`:

  `toSing G k (⋀ p a_p • p) = ∑ a_p • singGen (G ∘ esimp p)`.

This file collects the definitions and the scalar-action bookkeeping of the `ModuleCat` carriers
(the `ZSMul.toSMul` instance, `zsmul_eq_smul_cast`), so that `PlaneAff.lean` can stay purely
combinatorial.
-/
import Mathlib
import Submission.Work.BridgeSquare.PlaneAff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

-- The `ℤ`-module structure on the carrier of a `ModuleCat` is reached through `ZSMul.toSMul`;
-- making that instance the preferred one makes `map_smul`/`one_smul`/`map_sum` fire (the same
-- device as in `PsiM_truncCell_mem_range.lean` / `Endgame.lean`).
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The pushforward -/

/-- **The pushforward of an affine chain along `G`.** -/
def toSing {X : TopCat} (G : C(CuspE3, X)) (k : ℕ) : AffC k →ₗ[ℤ]
    (singCxFun.obj X).X k :=
  Finsupp.linearCombination ℤ fun p => singGen (G.comp (esimp p))

/-! ## §2  The differential on chains, as a linear map -/

theorem singCx_d_add {X : TopCat} (m n : ℕ) (x y : (singCxFun.obj X).X m) :
    (singCxFun.obj X).d m n (x + y)
      = (singCxFun.obj X).d m n x + (singCxFun.obj X).d m n y :=
  (ConcreteCategory.hom ((singCxFun.obj X).d m n)).map_add x y

theorem singCx_d_smul {X : TopCat} (m n : ℕ) (a : ℤ) (x : (singCxFun.obj X).X m) :
    (singCxFun.obj X).d m n (a • x) = a • ((singCxFun.obj X).d m n x) :=
  (ConcreteCategory.hom ((singCxFun.obj X).d m n)).map_smul a x

theorem singCx_d_sum {X : TopCat} (m n : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → (singCxFun.obj X).X m) :
    (singCxFun.obj X).d m n (∑ i ∈ s, f i) = ∑ i ∈ s, (singCxFun.obj X).d m n (f i) :=
  map_sum (ConcreteCategory.hom ((singCxFun.obj X).d m n)) f s

/-! ## §3  The generator formulas (delegated; see the files named below)

* `Work.BridgeSquare.planeToSingSingle` (`BridgeSquare/planeToSingSingle.lean`):
  `toSing G k (Finsupp.single p a) = a • singGen (G ∘ esimp p)`;
* `Work.BridgeSquare.planeSingGenD` (`BridgeSquare/planeSingGenD.lean`): the boundary formula for a
  singular generator, restated with the scalar action preferred here;
* `Work.BridgeSquare.planeToSingD` (`BridgeSquare/planeToSingD.lean`): the chain-map identity
  `∂ (toSing G c) = toSing G (dLC c)`.
-/

end

end Work.BridgeSquare
