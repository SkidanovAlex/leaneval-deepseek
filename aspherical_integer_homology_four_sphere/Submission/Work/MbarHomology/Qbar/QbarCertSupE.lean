/-
# The support checks for the sparse certificates of `Q̄`, part E (generated)

Faces 480 to 600.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupD

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
theorem hsupChunk_16 : ∀ f : Fin 865, 480 ≤ (f : ℕ) → (f : ℕ) < 510 → HsupFace f := by
  decide

theorem hsupChunk_17 : ∀ f : Fin 865, 510 ≤ (f : ℕ) → (f : ℕ) < 540 → HsupFace f := by
  decide

theorem hsupChunk_18 : ∀ f : Fin 865, 540 ≤ (f : ℕ) → (f : ℕ) < 570 → HsupFace f := by
  decide

theorem hsupChunk_19 : ∀ f : Fin 865, 570 ≤ (f : ℕ) → (f : ℕ) < 600 → HsupFace f := by
  decide

theorem hsupUpto_510 : ∀ f : Fin 865, (f : ℕ) < 510 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 480
  · exact hsupUpto_480 f h
  · exact hsupChunk_16 f (by omega) (by omega)

theorem hsupUpto_540 : ∀ f : Fin 865, (f : ℕ) < 540 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 510
  · exact hsupUpto_510 f h
  · exact hsupChunk_17 f (by omega) (by omega)

theorem hsupUpto_570 : ∀ f : Fin 865, (f : ℕ) < 570 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 540
  · exact hsupUpto_540 f h
  · exact hsupChunk_18 f (by omega) (by omega)

theorem hsupUpto_600 : ∀ f : Fin 865, (f : ℕ) < 600 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 570
  · exact hsupUpto_570 f h
  · exact hsupChunk_19 f (by omega) (by omega)

end Work.MbarHomology
