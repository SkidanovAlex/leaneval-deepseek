/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the Abel–Jacobi map `AJ₀ : C ⟶ G D`

The Abel–Jacobi map based at the origin: `x ↦ [x] - [P0]`, realised as
`curveAdd ≫ AJSym` (i.e. `x ↦ x + (g-1)P0` followed by the Abel–Jacobi morphism
`Sym^g C ⟶ G D`).
-/
import Submission.Work.GroupChunk.AJSym

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

namespace Input

variable [D : Input C P0]

/-- The degree of `ptDiv x - [P0]` is zero. -/
theorem ddeg_ptDiv_sub_bcKF_P0Div {F : Type u} [Field F] [Algebra K F]
    (x : FPt C.toOver F) : Ddeg C F (SpecLin.ptDiv x - bcKF F D.P0Div) = 0 := by
  have h1 : Ddeg C F (SpecLin.ptDiv x) = 1 := SpecLin.Points.ptDiv_deg x
  have h2 : Ddeg C F (bcKF F D.P0Div) = 1 := by
    rw [deg_bcKF, D.P0Div_deg]
  rw [map_sub, h1, h2, sub_self]

/-- **The Abel–Jacobi map** `AJ₀ : C ⟶ G D`, `x ↦ [x] - [P0]`. -/
def AJ₀ (D : Input C P0) : C.toOver ⟶ GSch D :=
  D.curveAdd ≫ D.AJSym

end Input

end

end Work.GroupChunk
