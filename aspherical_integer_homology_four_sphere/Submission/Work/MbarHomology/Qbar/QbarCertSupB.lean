/-
# The support checks for the sparse certificates of `Q̄`, part B (generated)

Faces 120 to 240.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupA

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
theorem hsupChunk_4 : ∀ f : Fin 865, 120 ≤ (f : ℕ) → (f : ℕ) < 150 → HsupFace f := by
  decide

theorem hsupChunk_5 : ∀ f : Fin 865, 150 ≤ (f : ℕ) → (f : ℕ) < 180 → HsupFace f := by
  decide

theorem hsupChunk_6 : ∀ f : Fin 865, 180 ≤ (f : ℕ) → (f : ℕ) < 210 → HsupFace f := by
  decide

theorem hsupChunk_7 : ∀ f : Fin 865, 210 ≤ (f : ℕ) → (f : ℕ) < 240 → HsupFace f := by
  decide

theorem hsupUpto_150 : ∀ f : Fin 865, (f : ℕ) < 150 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 120
  · exact hsupUpto_120 f h
  · exact hsupChunk_4 f (by omega) (by omega)

theorem hsupUpto_180 : ∀ f : Fin 865, (f : ℕ) < 180 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 150
  · exact hsupUpto_150 f h
  · exact hsupChunk_5 f (by omega) (by omega)

theorem hsupUpto_210 : ∀ f : Fin 865, (f : ℕ) < 210 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 180
  · exact hsupUpto_180 f h
  · exact hsupChunk_6 f (by omega) (by omega)

theorem hsupUpto_240 : ∀ f : Fin 865, (f : ℕ) < 240 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 210
  · exact hsupUpto_210 f h
  · exact hsupChunk_7 f (by omega) (by omega)

end Work.MbarHomology
