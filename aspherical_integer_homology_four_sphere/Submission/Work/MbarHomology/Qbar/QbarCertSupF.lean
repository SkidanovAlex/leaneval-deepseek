/-
# The support checks for the sparse certificates of `Q̄`, part F (generated)

Faces 600 to 720.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupE

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
theorem hsupChunk_20 : ∀ f : Fin 865, 600 ≤ (f : ℕ) → (f : ℕ) < 630 → HsupFace f := by
  decide

theorem hsupChunk_21 : ∀ f : Fin 865, 630 ≤ (f : ℕ) → (f : ℕ) < 660 → HsupFace f := by
  decide

theorem hsupChunk_22 : ∀ f : Fin 865, 660 ≤ (f : ℕ) → (f : ℕ) < 690 → HsupFace f := by
  decide

theorem hsupChunk_23 : ∀ f : Fin 865, 690 ≤ (f : ℕ) → (f : ℕ) < 720 → HsupFace f := by
  decide

theorem hsupUpto_630 : ∀ f : Fin 865, (f : ℕ) < 630 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 600
  · exact hsupUpto_600 f h
  · exact hsupChunk_20 f (by omega) (by omega)

theorem hsupUpto_660 : ∀ f : Fin 865, (f : ℕ) < 660 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 630
  · exact hsupUpto_630 f h
  · exact hsupChunk_21 f (by omega) (by omega)

theorem hsupUpto_690 : ∀ f : Fin 865, (f : ℕ) < 690 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 660
  · exact hsupUpto_660 f h
  · exact hsupChunk_22 f (by omega) (by omega)

theorem hsupUpto_720 : ∀ f : Fin 865, (f : ℕ) < 720 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 690
  · exact hsupUpto_690 f h
  · exact hsupChunk_23 f (by omega) (by omega)

end Work.MbarHomology
