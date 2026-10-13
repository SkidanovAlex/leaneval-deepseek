/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *coordinate bookkeeping* of
  the Rolle step `Work.WilE3K.ET_rolle_step`.

  Everything here is elementary reshuffling of the `Fin`-indices of an `ETData`:
  * `psiMap` is the system map with the eliminated row (`E.lastRow`) deleted, so its coordinates are
    the arctan equations `j < rt` and the polynomial equations `i : Fin n`;
  * the new system `E.newData y δ` has the same chain as `E` (`newData_evalPoly`), its arctan
    equations are the old ones shifted by the level value `y`, and its new polynomial equation
    `i' = 0` is the Rolle equation;
  * `E.psiLift y` is the value of the full map at the point of the level set `{psiMap = y}`, so
    `E.map z = E.psiLift y ↔ E.psiMap z = y ∧ E.gLast z = 0`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE3K.evalPoly_rolleDetP

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-! ## §0. A `Fin` helper: the complement of `succAbove` -/

theorem exists_succAbove_eq {m : ℕ} (p r : Fin (m + 1)) (h : r ≠ p) :
    ∃ i : Fin m, p.succAbove i = r := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · -- `r < p`
    refine ⟨⟨(r : ℕ), by omega⟩, ?_⟩
    have h2 : (⟨(r : ℕ), by omega⟩ : Fin m).succ ≤ p := by
      simp only [Fin.le_def, Fin.val_succ]
      omega
    rw [Fin.succAbove_of_succ_le p _ h2]
    exact Fin.ext (by simp only [Fin.val_castSucc])
  · -- `p < r`
    refine ⟨⟨(r : ℕ) - 1, by omega⟩, ?_⟩
    have h2 : p ≤ (⟨(r : ℕ) - 1, by omega⟩ : Fin m).castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc p _ h2]
    exact Fin.ext (by simp only [Fin.val_succ]; omega)

namespace ETData

variable (E : ETData N (rt + 1) n re)

/-! ## §1. The map, `psiMap`, `gLast` -/

/-- The value of the full map on the eliminated row is the eliminated equation. -/
theorem map_lastRow (z : Fin (N + 1) → ℝ) : E.map z E.lastRow = E.gLast z := by
  have h : E.lastRow = E.tanCoord (Fin.last rt) := Fin.ext rfl
  rw [h, E.map_tan]
  rfl

/-- **The coordinates of the remaining system.**  `psiMap` is the system map with the eliminated row
(`lastRow`) deleted: its coordinates are the arctan equations `j < rt` and the polynomial
equations `i : Fin n`. -/
theorem psiMap_apply_tan (z : Fin (N + 1) → ℝ) (j : Fin rt) :
    E.psiMap z (Fin.castLE (by have h := E.h; omega) j) = E.tanFun (Fin.castSucc j) z := by
  rw [ETData.psiMap_apply]
  have h1 : (Fin.castLE (by have h := E.h; omega) j : Fin N).succ ≤ E.lastRow := by
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castLE, ETData.lastRow]
    exact j.isLt
  rw [Fin.succAbove_of_succ_le E.lastRow _ h1]
  rw [show (Fin.castLE (by have h := E.h; omega) j : Fin N).castSucc
      = E.tanCoord (Fin.castSucc j) from Fin.ext rfl, E.map_tan]

/-- The `i`-th free coordinate of the remaining system is the `i`-th polynomial equation. -/
theorem psiMap_apply_free (z : Fin (N + 1) → ℝ) (i : Fin n) :
    E.psiMap z (Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt i)) = E.evP i z := by
  rw [ETData.psiMap_apply]
  have h1 : E.lastRow
      ≤ (Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt i) : Fin N).castSucc := by
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_castLE, Fin.val_natAdd, ETData.lastRow]
    omega
  rw [Fin.succAbove_of_le_castSucc E.lastRow _ h1]
  have h2 : (Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt i) : Fin N).succ
      = E.freeCoord i := by
    refine Fin.ext ?_
    simp only [Fin.val_succ, Fin.val_castLE, Fin.val_natAdd, ETData.freeCoord_val]
    omega
  rw [h2, E.map_free]

/-- **The fibre of the full map over the value `psiLift y` is the set of crossings of the level
set `{psiMap = y}` with the eliminated equation.** -/
theorem map_eq_psiLift_iff (y : Fin N → ℝ) (z : Fin (N + 1) → ℝ) :
    E.map z = E.psiLift y ↔ E.psiMap z = y ∧ E.gLast z = 0 := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, ?_⟩
    · have h1 := congrFun h (Fin.succAbove E.lastRow i)
      rw [E.psiLift_succAbove] at h1
      rw [ETData.psiMap_apply]
      exact h1
    · have h1 := congrFun h E.lastRow
      rw [E.psiLift_lastRow, E.map_lastRow] at h1
      exact h1
  · rintro ⟨h1, h2⟩
    funext r
    by_cases hr : r = E.lastRow
    · subst hr
      rw [E.map_lastRow, h2, E.psiLift_lastRow]
    · obtain ⟨i, hi⟩ := exists_succAbove_eq E.lastRow r hr
      have hpsi : E.psiLift y r = y i := by rw [← hi, E.psiLift_succAbove]
      rw [hpsi, ← hi, ← congrFun h1 i, ETData.psiMap_apply]

/-! ## §2. The new system: same chain, new equations -/

/-- The chain coefficient of the new system vanishes on the new (eliminated) coordinate. -/
@[simp] theorem newCa_zero (y : Fin N → ℝ) (δ : ℝ) (j : Fin re) :
    (E.newData y δ).ca j 0 = 0 := by
  simp only [ETData.newData, ETData.newCa]
  simp

/-- The chain coefficients of the new system are the old ones (shifted by one). -/
theorem newCa_succ (y : Fin N → ℝ) (δ : ℝ) (j : Fin re) (i : Fin n) :
    (E.newData y δ).ca j i.succ = E.ca j i := by
  have hne : ¬ ((i.succ : Fin (n + 1)) : ℕ) = 0 := by
    simp only [Fin.val_succ]
    omega
  simp only [ETData.newData, ETData.newCa]
  rw [dif_neg hne]
  exact congrArg (E.ca j) (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- The new free coordinates are the old ones (shifted by one). -/
theorem newData_freeCoord_succ (y : Fin N → ℝ) (δ : ℝ) (i : Fin n) :
    (E.newData y δ).freeCoord i.succ = E.freeCoord i := by
  refine Fin.ext ?_
  simp only [ETData.freeCoord_val, Fin.val_succ]
  omega

/-- The new free coordinate of index `0` is the eliminated arctan coordinate. -/
theorem newData_freeCoord_zero (y : Fin N → ℝ) (δ : ℝ) :
    (E.newData y δ).freeCoord 0 = E.lastRow := by
  refine Fin.ext ?_
  simp only [ETData.freeCoord_val, ETData.lastRow]
  simp

/-- The new arctan coordinates are the old ones. -/
theorem newData_tanCoord (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) :
    (E.newData y δ).tanCoord j = E.tanCoord (Fin.castSucc j) := by
  refine Fin.ext ?_
  simp only [ETData.tanCoord_val, Fin.val_castSucc]

/-- **The chain of the new system is the chain of the old one.** -/
theorem newData_ellChain (y : Fin N → ℝ) (δ : ℝ) (j : Fin re) (z : Fin (N + 1) → ℝ) :
    (E.newData y δ).ellChain j z = E.ellChain j z := by
  rw [ETData.ellChain, ETData.ellChain, Fin.sum_univ_succ]
  have hzero : (E.newData y δ).ca j 0 * z ((E.newData y δ).freeCoord 0) = 0 := by
    rw [E.newCa_zero, zero_mul]
  have hsucc : ∀ i : Fin n,
      (E.newData y δ).ca j i.succ * z ((E.newData y δ).freeCoord i.succ)
        = E.ca j i * z (E.freeCoord i) := by
    intro i
    rw [E.newCa_succ y δ j i, E.newData_freeCoord_succ y δ i]
  rw [hzero, zero_add, Finset.sum_congr rfl (fun i _ => hsucc i)]
  rfl

/-- **Evaluation of an `EA`-polynomial on the new system is evaluation on the old one.** -/
theorem newData_evalPoly (y : Fin N → ℝ) (δ : ℝ) (P : EAPoly (N + 1) re)
    (z : Fin (N + 1) → ℝ) : (E.newData y δ).evalPoly P z = E.evalPoly P z := by
  simp only [ETData.evalPoly]
  have h : (Sum.elim z fun j => Real.exp ((E.newData y δ).ellChain j z))
      = (Sum.elim z fun j => Real.exp (E.ellChain j z)) := by
    funext s
    rcases s with k | j
    · rfl
    · simp only [Sum.elim_inr, E.newData_ellChain]
  rw [h]

end ETData

end Work.WilE3K
