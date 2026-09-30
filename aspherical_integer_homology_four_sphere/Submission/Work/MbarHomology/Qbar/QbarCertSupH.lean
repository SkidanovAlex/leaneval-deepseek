/-
# The support checks for the sparse certificates of `Q̄`, part H (generated)

Faces 840 to 865.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs
import Submission.Work.MbarHomology.Qbar.QbarCertSupG

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
theorem hsupChunk_28 : ∀ f : Fin 865, 840 ≤ (f : ℕ) → (f : ℕ) < 870 → HsupFace f := by
  decide +kernel

theorem hsupUpto_870 : ∀ f : Fin 865, (f : ℕ) < 870 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 840
  · exact hsupUpto_840 f h
  · exact hsupChunk_28 f (by omega) (by omega)

/-- the support conditions for every face of `QbarPD` -/
theorem hsupAll : ∀ (f : Fin 865) (i : Fin 48), empSelB f i = true →
    empPat f i < 888 ∧ i ∉ qTight f ∧ empC1 f i ≠ empC2 f i ∧
      ({empC1 f i, empC2 f i} : Finset (Fin 48)) ⊆ qTight f ∪ {i} := by
  intro f i h
  exact hsupUpto_870 f (by omega) i h

end Work.MbarHomology
