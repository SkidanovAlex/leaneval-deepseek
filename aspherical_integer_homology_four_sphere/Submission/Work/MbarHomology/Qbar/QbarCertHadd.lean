/-
# The nonempty-case check for the sparse certificates of `Q̄` (generated)

For every face `f` and constraint `i` with `empSelB f i = false` the region `Fset f ∩ {i tight}` is
nonempty with tight set `qTight f ∪ {i}`, realised by `empAddIdx f i`.  This is the `hadd`
hypothesis of `Work.MbarHomology.Qbar.Carriers_of_sparse`.  Checked by `decide` in chunks of 100.
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

/-- the nonempty case for one face -/
abbrev HaddFace (f : Fin 865) : Prop :=
  ∀ i : Fin 48, empSelB f i = false → qTight (empAddIdx f i) = qTight f ∪ {i}

theorem haddChunk_0 : ∀ f : Fin 865, 0 ≤ (f : ℕ) → (f : ℕ) < 100 → HaddFace f := by
  decide

theorem haddChunk_1 : ∀ f : Fin 865, 100 ≤ (f : ℕ) → (f : ℕ) < 200 → HaddFace f := by
  decide

theorem haddChunk_2 : ∀ f : Fin 865, 200 ≤ (f : ℕ) → (f : ℕ) < 300 → HaddFace f := by
  decide

theorem haddChunk_3 : ∀ f : Fin 865, 300 ≤ (f : ℕ) → (f : ℕ) < 400 → HaddFace f := by
  decide

theorem haddChunk_4 : ∀ f : Fin 865, 400 ≤ (f : ℕ) → (f : ℕ) < 500 → HaddFace f := by
  decide

theorem haddChunk_5 : ∀ f : Fin 865, 500 ≤ (f : ℕ) → (f : ℕ) < 600 → HaddFace f := by
  decide

theorem haddChunk_6 : ∀ f : Fin 865, 600 ≤ (f : ℕ) → (f : ℕ) < 700 → HaddFace f := by
  decide

theorem haddChunk_7 : ∀ f : Fin 865, 700 ≤ (f : ℕ) → (f : ℕ) < 800 → HaddFace f := by
  decide

theorem haddChunk_8 : ∀ f : Fin 865, 800 ≤ (f : ℕ) → (f : ℕ) < 900 → HaddFace f := by
  decide

theorem haddUpto_100 : ∀ f : Fin 865, (f : ℕ) < 100 → HaddFace f :=
  fun f hf => haddChunk_0 f (Nat.zero_le _) hf

theorem haddUpto_200 : ∀ f : Fin 865, (f : ℕ) < 200 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 100
  · exact haddUpto_100 f h
  · exact haddChunk_1 f (by omega) (by omega)

theorem haddUpto_300 : ∀ f : Fin 865, (f : ℕ) < 300 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 200
  · exact haddUpto_200 f h
  · exact haddChunk_2 f (by omega) (by omega)

theorem haddUpto_400 : ∀ f : Fin 865, (f : ℕ) < 400 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 300
  · exact haddUpto_300 f h
  · exact haddChunk_3 f (by omega) (by omega)

theorem haddUpto_500 : ∀ f : Fin 865, (f : ℕ) < 500 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 400
  · exact haddUpto_400 f h
  · exact haddChunk_4 f (by omega) (by omega)

theorem haddUpto_600 : ∀ f : Fin 865, (f : ℕ) < 600 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 500
  · exact haddUpto_500 f h
  · exact haddChunk_5 f (by omega) (by omega)

theorem haddUpto_700 : ∀ f : Fin 865, (f : ℕ) < 700 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 600
  · exact haddUpto_600 f h
  · exact haddChunk_6 f (by omega) (by omega)

theorem haddUpto_800 : ∀ f : Fin 865, (f : ℕ) < 800 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 700
  · exact haddUpto_700 f h
  · exact haddChunk_7 f (by omega) (by omega)

theorem haddUpto_900 : ∀ f : Fin 865, (f : ℕ) < 900 → HaddFace f := by
  intro f hf
  by_cases h : (f : ℕ) < 800
  · exact haddUpto_800 f h
  · exact haddChunk_8 f (by omega) (by omega)

/-- the nonempty case for every face of `QbarPD` -/
theorem haddAll : ∀ f : Fin 865, HaddFace f := by
  intro f
  exact haddUpto_900 f (by omega)

end Work.MbarHomology
