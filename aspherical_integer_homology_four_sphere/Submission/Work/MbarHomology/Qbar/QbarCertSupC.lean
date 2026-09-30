/-
# The support checks for the sparse certificates of `Q̄`, part C (generated)

Faces 240 to 360.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupB

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
theorem hsupChunk_8 : ∀ f : Fin 865, 240 ≤ (f : ℕ) → (f : ℕ) < 270 → HsupFace f := by
  decide

theorem hsupChunk_9 : ∀ f : Fin 865, 270 ≤ (f : ℕ) → (f : ℕ) < 300 → HsupFace f := by
  decide

theorem hsupChunk_10 : ∀ f : Fin 865, 300 ≤ (f : ℕ) → (f : ℕ) < 330 → HsupFace f := by
  decide

theorem hsupChunk_11 : ∀ f : Fin 865, 330 ≤ (f : ℕ) → (f : ℕ) < 360 → HsupFace f := by
  decide

theorem hsupUpto_270 : ∀ f : Fin 865, (f : ℕ) < 270 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 240
  · exact hsupUpto_240 f h
  · exact hsupChunk_8 f (by omega) (by omega)

theorem hsupUpto_300 : ∀ f : Fin 865, (f : ℕ) < 300 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 270
  · exact hsupUpto_270 f h
  · exact hsupChunk_9 f (by omega) (by omega)

theorem hsupUpto_330 : ∀ f : Fin 865, (f : ℕ) < 330 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 300
  · exact hsupUpto_300 f h
  · exact hsupChunk_10 f (by omega) (by omega)

theorem hsupUpto_360 : ∀ f : Fin 865, (f : ℕ) < 360 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 330
  · exact hsupUpto_330 f h
  · exact hsupChunk_11 f (by omega) (by omega)

end Work.MbarHomology
