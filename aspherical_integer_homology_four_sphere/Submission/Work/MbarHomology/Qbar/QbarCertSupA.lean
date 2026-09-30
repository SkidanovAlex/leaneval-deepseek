/-
# The support checks for the sparse certificates of `Q̄`, part A (generated)

Faces 0 to 120.  See `QbarCertSupA.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs

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

/-- the support conditions for one face -/
abbrev HsupFace (f : Fin 865) : Prop :=
  ∀ i : Fin 48, empSelB f i = true →
    empPat f i < 888 ∧ i ∉ qTight f ∧ empC1 f i ≠ empC2 f i ∧
      ({empC1 f i, empC2 f i} : Finset (Fin 48)) ⊆ qTight f ∪ {i}

theorem hsupChunk_0 : ∀ f : Fin 865, 0 ≤ (f : ℕ) → (f : ℕ) < 30 → HsupFace f := by
  decide

theorem hsupChunk_1 : ∀ f : Fin 865, 30 ≤ (f : ℕ) → (f : ℕ) < 60 → HsupFace f := by
  decide

theorem hsupChunk_2 : ∀ f : Fin 865, 60 ≤ (f : ℕ) → (f : ℕ) < 90 → HsupFace f := by
  decide

theorem hsupChunk_3 : ∀ f : Fin 865, 90 ≤ (f : ℕ) → (f : ℕ) < 120 → HsupFace f := by
  decide

theorem hsupUpto_30 : ∀ f : Fin 865, (f : ℕ) < 30 → HsupFace f :=
  fun f hf => hsupChunk_0 f (Nat.zero_le _) hf

theorem hsupUpto_60 : ∀ f : Fin 865, (f : ℕ) < 60 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 30
  · exact hsupUpto_30 f h
  · exact hsupChunk_1 f (by omega) (by omega)

theorem hsupUpto_90 : ∀ f : Fin 865, (f : ℕ) < 90 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 60
  · exact hsupUpto_60 f h
  · exact hsupChunk_2 f (by omega) (by omega)

theorem hsupUpto_120 : ∀ f : Fin 865, (f : ℕ) < 120 → HsupFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 90
  · exact hsupUpto_90 f h
  · exact hsupChunk_3 f (by omega) (by omega)

end Work.MbarHomology
