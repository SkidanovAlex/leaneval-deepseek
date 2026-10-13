/-
  WilG1 / Cell / Junk / fibBad_thin_defs.

  Vocabulary for reducing a fibre of a definable function in an arbitrary coordinate direction
  to the *last* coordinate direction, which is the form in which the one-dimensional thinness
  theorem (`partialBad_thin`) is available.

  `insPerm m i : Fin (m + 1) ≃ Fin (m + 1)` moves the index `i` to the last position: it sends
  `i` to `Fin.last m` and `i.succAbove k` to `k.castSucc`.  Consequently, for
  `x : Fin (m + 1) → ℝ` the reindexed tuple `x ∘ insPerm m i` is obtained from `x` by
  *inserting* the last coordinate of `x` at position `i`
  (`comp_insPerm_eq_insertNth`), and conversely `y ∘ (insPerm m i)⁻¹` re-inserts the `i`-th
  coordinate of `y` at the last position (`comp_insPerm_symm_eq_snoc`).  Hence the `i`-th fibre
  of `h` is the last fibre of `x ↦ h (x ∘ insPerm m i)`.

  `insPermLift m i` is the same index permutation lifted to `Fin (m + 2)` (it fixes the value
  coordinate), so that reindexing a graph by `insPerm` is reindexing it by `insPermLift` in one
  dimension higher; see `Work.WilG1.Cell.Junk.graphOf_comp_insPerm`.
-/
import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Plumb.Imports

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG1.Cell.Junk

open WilkiesDesign Work.WilG1

/-- The index transposition of `Fin (m + 1)` moving `i` to the last position. -/
def insFun (m : ℕ) (i : Fin (m + 1)) : Fin (m + 1) → Fin (m + 1) :=
  fun a => @Fin.insertNth m (fun _ : Fin (m + 1) => Fin (m + 1)) i (Fin.last m)
    (fun k => Fin.castSucc k) a

/-- The inverse index transposition: it moves the last position to `i`. -/
def invFun (m : ℕ) (i : Fin (m + 1)) : Fin (m + 1) → Fin (m + 1) :=
  fun a => Fin.lastCases i (fun k => i.succAbove k) a

@[simp] lemma insFun_self (m : ℕ) (i : Fin (m + 1)) : insFun m i i = Fin.last m := by
  simp [insFun]

@[simp] lemma insFun_succAbove (m : ℕ) (i : Fin (m + 1)) (k : Fin m) :
    insFun m i (i.succAbove k) = Fin.castSucc k := by
  simp [insFun]

@[simp] lemma invFun_last (m : ℕ) (i : Fin (m + 1)) : invFun m i (Fin.last m) = i := by
  simp [invFun]

@[simp] lemma invFun_castSucc (m : ℕ) (i : Fin (m + 1)) (k : Fin m) :
    invFun m i (Fin.castSucc k) = i.succAbove k := by
  simp [invFun]

/-- `insPerm m i` moves the index `i` of `Fin (m + 1)` to the last position (and the indices
`i.succAbove k` to the positions `k.castSucc`). -/
def insPerm (m : ℕ) (i : Fin (m + 1)) : Fin (m + 1) ≃ Fin (m + 1) where
  toFun := insFun m i
  invFun := invFun m i
  left_inv a := by
    rcases Fin.eq_self_or_eq_succAbove i a with rfl | ⟨k, rfl⟩ <;> simp
  right_inv a := by
    cases a using Fin.lastCases <;> simp

@[simp] lemma insPerm_self (m : ℕ) (i : Fin (m + 1)) : insPerm m i i = Fin.last m := by
  simp [insPerm]

@[simp] lemma insPerm_succAbove (m : ℕ) (i : Fin (m + 1)) (k : Fin m) :
    insPerm m i (i.succAbove k) = Fin.castSucc k := by
  simp [insPerm]

@[simp] lemma insPerm_symm_last (m : ℕ) (i : Fin (m + 1)) :
    (insPerm m i).symm (Fin.last m) = i := by
  simp [insPerm]

@[simp] lemma insPerm_symm_castSucc (m : ℕ) (i : Fin (m + 1)) (k : Fin m) :
    (insPerm m i).symm (Fin.castSucc k) = i.succAbove k := by
  simp [insPerm]

/-- Reindexing a tuple by `insPerm m i` inserts its last coordinate at position `i`. -/
lemma comp_insPerm_eq_insertNth (m : ℕ) (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
    x ∘ (insPerm m i : Fin (m + 1) → Fin (m + 1)) =
      Fin.insertNth i (x (Fin.last m)) (fun k => x (Fin.castSucc k)) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp

/-- Reindexing a tuple by the inverse of `insPerm m i` moves its `i`-th coordinate to the last
position; explicitly this is `Fin.snoc` of the remaining coordinates. -/
lemma comp_insPerm_symm_eq_snoc (m : ℕ) (i : Fin (m + 1)) (y : Fin (m + 1) → ℝ) :
    y ∘ ((insPerm m i).symm : Fin (m + 1) → Fin (m + 1)) =
      Fin.snoc (Fin.removeNth i y) (y i) := by
  funext j
  cases j using Fin.lastCases <;> simp [Fin.removeNth_apply]

/-- The index permutation `insPerm m i` of the parameter coordinates, lifted to `Fin (m + 2)` by
fixing the value coordinate. -/
def insPermLift (m : ℕ) (i : Fin (m + 1)) : Fin (m + 2) → Fin (m + 2) :=
  Fin.snoc (fun j : Fin (m + 1) => Fin.castSucc (insPerm m i j)) (Fin.last (m + 1))

@[simp] lemma insPermLift_last (m : ℕ) (i : Fin (m + 1)) :
    insPermLift m i (Fin.last (m + 1)) = Fin.last (m + 1) := by
  simp [insPermLift]

@[simp] lemma insPermLift_castSucc (m : ℕ) (i : Fin (m + 1)) (j : Fin (m + 1)) :
    insPermLift m i (Fin.castSucc j) = Fin.castSucc (insPerm m i j) := by
  simp [insPermLift]

end Work.WilG1.Cell.Junk
