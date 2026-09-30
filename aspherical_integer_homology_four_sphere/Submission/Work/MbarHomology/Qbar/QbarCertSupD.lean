/-
# The support checks for the sparse certificates of `Q̄`, part D (generated)

Faces 360 to 480.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option autoImplicit false

namespace Work.MbarHomology

open scoped BigOperators
theorem hsupChunk_12 : ∀ f : Fin 865, 360 ≤ (f : ℕ) → (f : ℕ) < 390 → HsupFace f := by
  decide +kernel

theorem hsupChunk_13 : ∀ f : Fin 865, 390 ≤ (f : ℕ) → (f : ℕ) < 420 → HsupFace f := by
  decide +kernel

theorem hsupChunk_14 : ∀ f : Fin 865, 420 ≤ (f : ℕ) → (f : ℕ) < 450 → HsupFace f := by
  decide +kernel

theorem hsupChunk_15 : ∀ f : Fin 865, 450 ≤ (f : ℕ) → (f : ℕ) < 480 → HsupFace f := by
  decide +kernel

theorem hsupUpto_390 : ∀ f : Fin 865, (f : ℕ) < 390 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 360
  · exact hsupUpto_360 f h
  · exact hsupChunk_12 f (by omega) (by omega)

theorem hsupUpto_420 : ∀ f : Fin 865, (f : ℕ) < 420 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 390
  · exact hsupUpto_390 f h
  · exact hsupChunk_13 f (by omega) (by omega)

theorem hsupUpto_450 : ∀ f : Fin 865, (f : ℕ) < 450 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 420
  · exact hsupUpto_420 f h
  · exact hsupChunk_14 f (by omega) (by omega)

theorem hsupUpto_480 : ∀ f : Fin 865, (f : ℕ) < 480 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 450
  · exact hsupUpto_450 f h
  · exact hsupChunk_15 f (by omega) (by omega)

end Work.MbarHomology
