/-
# The support checks for the sparse certificates of `Q̄`, part G (generated)

Faces 720 to 840.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupF

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
theorem hsupChunk_24 : ∀ f : Fin 865, 720 ≤ (f : ℕ) → (f : ℕ) < 750 → HsupFace f := by
  decide +kernel

theorem hsupChunk_25 : ∀ f : Fin 865, 750 ≤ (f : ℕ) → (f : ℕ) < 780 → HsupFace f := by
  decide +kernel

theorem hsupChunk_26 : ∀ f : Fin 865, 780 ≤ (f : ℕ) → (f : ℕ) < 810 → HsupFace f := by
  decide +kernel

theorem hsupChunk_27 : ∀ f : Fin 865, 810 ≤ (f : ℕ) → (f : ℕ) < 840 → HsupFace f := by
  decide +kernel

theorem hsupUpto_750 : ∀ f : Fin 865, (f : ℕ) < 750 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 720
  · exact hsupUpto_720 f h
  · exact hsupChunk_24 f (by omega) (by omega)

theorem hsupUpto_780 : ∀ f : Fin 865, (f : ℕ) < 780 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 750
  · exact hsupUpto_750 f h
  · exact hsupChunk_25 f (by omega) (by omega)

theorem hsupUpto_810 : ∀ f : Fin 865, (f : ℕ) < 810 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 780
  · exact hsupUpto_780 f h
  · exact hsupChunk_26 f (by omega) (by omega)

theorem hsupUpto_840 : ∀ f : Fin 865, (f : ℕ) < 840 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 810
  · exact hsupUpto_810 f h
  · exact hsupChunk_27 f (by omega) (by omega)

end Work.MbarHomology
