/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the **graph chart of the last
  `tan` coordinate**, the vocabulary of `Work.WilE3K.ETReg_bad_null`.

  For `E : ETData N (rt+1) n re` the eliminated arctan equation is `E.gLast = E.tanFun (Fin.last rt)`
  (`Elim.lean`), whose zero set is the graph of
  `t ↦ tan (∑_j lam_j x_j + mu_j)` over the free coordinates.  This file introduces

  * `freeIdx j : Fin N` — the position of the `j`-th free coordinate inside `Fin N` (the free
    coordinates are the coordinates `≠ E.lastRow`, and `E.freeIdx` is the inverse of
    `E.lastRow.succAbove` on that set: `succAbove_freeIdx`);
  * `outIdx r _ : Fin N` — the inverse of `E.lastRow.succAbove` (`succAbove_outIdx`);
  * `ell x = ∑_j lam_j * x_j + mu_j` (`E.lin (Fin.last rt)` after the substitution) and its
    derivative `dell`;
  * `chart x` — the point whose free coordinates are `x` and whose `lastRow` coordinate is
    `Real.tan (ell x)`;  `chartDom = {x | -(π/2) < ell x ∧ ell x < π/2}` — the open set on which
    `chart` inverts `E.gLast` (`gLast_chart`), and `chartMap = E.psiMap ∘ E.chart` — the *square*
    map of the graph chart;
  * `dchart x` — the explicit derivative of `chart`, and the explicit derivatives
    `djac z r = ∑_c (jac z r c) • proj c`, `dmap z`, `dpsi z`, `dgLast z`, `dG x` of
    `E.map`, `E.psiMap`, `E.gLast` and `E.chartMap`.

  All the analytic content (`HasFDerivAt` statements) lives in the modules of `Submission/Work/`;
  this file only fixes the vocabulary.
-/
import Mathlib
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETData

variable {N rt n re : ℕ}

/-! ## §1. Index bookkeeping: the inverse of `E.lastRow.succAbove` -/

/-- The position of the `j`-th free coordinate inside `Fin N` (i.e. inside the source of the
chart): `E.lastRow.succAbove (E.freeIdx j) = E.freeCoord j`. -/
def freeIdx (E : ETData N (rt + 1) n re) (j : Fin n) : Fin N :=
  ⟨rt + j, by have h := E.h; omega⟩

@[simp] theorem freeIdx_val (E : ETData N (rt + 1) n re) (j : Fin n) :
    ((E.freeIdx j : Fin N) : ℕ) = rt + j := rfl

theorem freeIdx_injective (E : ETData N (rt + 1) n re) : Function.Injective E.freeIdx := by
  intro a b hab
  have h : rt + (a : ℕ) = rt + (b : ℕ) := by
    have := congrArg Fin.val hab
    simpa using this
  exact Fin.ext (by omega)

/-- The inverse of `E.lastRow.succAbove` away from `E.lastRow`. -/
def outIdx (E : ETData N (rt + 1) n re) (r : Fin (N + 1)) (hr : r ≠ E.lastRow) : Fin N :=
  if h : (r : ℕ) < rt then ⟨r, by have hh := E.h; omega⟩
  else ⟨(r : ℕ) - 1, by
    have hh := E.h
    have h1 : rt ≤ (r : ℕ) := not_lt.mp h
    have h2 : (r : ℕ) ≠ rt := fun hc => hr (Fin.ext (by simpa [lastRow] using hc))
    have h3 : (r : ℕ) < N + 1 := r.isLt
    omega⟩

theorem succAbove_outIdx (E : ETData N (rt + 1) n re) (r : Fin (N + 1)) (hr : r ≠ E.lastRow) :
    E.lastRow.succAbove (E.outIdx r hr) = r := by
  have hh := E.h
  have h2 : (r : ℕ) ≠ rt := fun hc => hr (Fin.ext (by simpa [lastRow] using hc))
  have h3 : (r : ℕ) < N + 1 := r.isLt
  unfold outIdx
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt]
    · exact Fin.ext rfl
    · simp only [Fin.lt_def, Fin.val_castSucc]; exact h
  · rw [Fin.succAbove_of_le_castSucc]
    · apply Fin.ext
      simp only [Fin.val_succ]
      omega
    · simp only [Fin.le_def, Fin.val_castSucc, lastRow]; omega

theorem outIdx_succAbove (E : ETData N (rt + 1) n re) (i : Fin N) :
    E.outIdx (E.lastRow.succAbove i) (Fin.succAbove_ne E.lastRow i) = i := by
  apply Fin.succAbove_right_injective (p := E.lastRow)
  rw [E.succAbove_outIdx]

theorem succAbove_freeIdx (E : ETData N (rt + 1) n re) (j : Fin n) :
    E.lastRow.succAbove (E.freeIdx j) = E.freeCoord j := by
  have hh := E.h
  rw [Fin.succAbove_of_le_castSucc]
  · apply Fin.ext
    simp only [Fin.val_succ, freeIdx_val, freeCoord_val]
    omega
  · simp only [Fin.le_def, Fin.val_castSucc, lastRow, freeIdx_val]; omega

theorem freeCoord_ne_lastRow (E : ETData N (rt + 1) n re) (j : Fin n) :
    E.freeCoord j ≠ E.lastRow := by
  intro h
  have h1 : ((E.freeCoord j : Fin (N + 1)) : ℕ) = rt + 1 + j := rfl
  have h2 : ((E.lastRow : Fin (N + 1)) : ℕ) = rt := rfl
  rw [h] at h1
  omega

theorem outIdx_freeCoord (E : ETData N (rt + 1) n re) (j : Fin n)
    (hr : E.freeCoord j ≠ E.lastRow) : E.outIdx (E.freeCoord j) hr = E.freeIdx j := by
  apply Fin.succAbove_right_injective (p := E.lastRow)
  rw [E.succAbove_outIdx, E.succAbove_freeIdx]

/-! ## §2. The chart -/

/-- The derivative of `ℓ` (a constant linear functional on the free coordinates). -/
def dell (E : ETData N (rt + 1) n re) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin n, E.lam (Fin.last rt) j •
    (ContinuousLinearMap.proj (E.freeIdx j) : (Fin N → ℝ) →L[ℝ] ℝ)

/-- `ℓ x = E.lin (Fin.last rt)` at the point of the chart with free coordinates `x`. -/
def ell (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) : ℝ :=
  (∑ j : Fin n, E.lam (Fin.last rt) j * x (E.freeIdx j)) + E.mu (Fin.last rt)

/-- The graph chart of the eliminated arctan equation: the free coordinates are `x`, the
`lastRow` coordinate is `Real.tan (ℓ x)`. -/
def chart (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  fun r => if h : r = E.lastRow then Real.tan (E.ell x) else x (E.outIdx r h)

/-- The domain of the chart: the points where `ℓ` lies in the fundamental slab of `tan`. -/
def chartDom (E : ETData N (rt + 1) n re) : Set (Fin N → ℝ) :=
  {x | -(Real.pi / 2) < E.ell x ∧ E.ell x < Real.pi / 2}

/-- The square map of the graph chart: `E.psiMap` composed with `E.chart`. -/
def chartMap (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) : Fin N → ℝ :=
  E.psiMap (E.chart x)

/-- The explicit derivative of `chart`. -/
def dchart (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin (N + 1) → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    if h : r = E.lastRow then (1 + Real.tan (E.ell x) ^ 2) • E.dell
    else (ContinuousLinearMap.proj (E.outIdx r h) : (Fin N → ℝ) →L[ℝ] ℝ)

@[simp] theorem chart_lastRow (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) :
    E.chart x E.lastRow = Real.tan (E.ell x) := by
  rw [chart]; exact dif_pos rfl

theorem chart_of_ne (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) {r : Fin (N + 1)}
    (h : r ≠ E.lastRow) : E.chart x r = x (E.outIdx r h) := by
  rw [chart]; exact dif_neg h

theorem chart_succAbove (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) (i : Fin N) :
    E.chart x (E.lastRow.succAbove i) = x i := by
  have h := Fin.succAbove_ne E.lastRow i
  rw [E.chart_of_ne x h]
  congr 1
  exact E.outIdx_succAbove i

@[simp] theorem dchart_apply_lastRow (E : ETData N (rt + 1) n re) (x : Fin N → ℝ)
    (v : Fin N → ℝ) :
    E.dchart x v E.lastRow = (1 + Real.tan (E.ell x) ^ 2) * E.dell v := by
  simp only [dchart]
  rw [ContinuousLinearMap.pi_apply, dif_pos rfl, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem dchart_apply_succAbove (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) (i : Fin N)
    (v : Fin N → ℝ) : E.dchart x v (E.lastRow.succAbove i) = v i := by
  simp only [dchart]
  rw [ContinuousLinearMap.pi_apply, dif_neg (Fin.succAbove_ne E.lastRow i),
    ContinuousLinearMap.proj_apply]
  exact congrArg v (E.outIdx_succAbove i)

/-! ## §3. The derivatives of the system maps -/

/-- The `r`-th row of the Jacobian, as a continuous linear functional on the ambient space. -/
def djac (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) (r : Fin (N + 1)) :
    (Fin (N + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ c : Fin (N + 1), E.jac z r c •
    (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)

/-- The derivative of `E.map` at `z`. -/
def dmap (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ) := ContinuousLinearMap.pi (E.djac z)

/-- The derivative of `E.psiMap` at `z` (the rows of `dmap` other than `E.lastRow`). -/
def dpsi (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => E.djac z (E.lastRow.succAbove i)

/-- The derivative of the eliminated arctan equation `E.gLast` at `z`. -/
def dgLast (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] ℝ := E.djac z E.lastRow

/-- The derivative of `E.chartMap` at `x` (the chain rule combination of `dpsi` and `dchart`). -/
def dG (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (E.dpsi (E.chart x)).comp (E.dchart x)

@[simp] theorem djac_apply (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (r : Fin (N + 1)) (v : Fin (N + 1) → ℝ) :
    E.djac z r v = ∑ c, E.jac z r c * v c := by
  simp only [djac, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

@[simp] theorem dmap_apply (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (v : Fin (N + 1) → ℝ) (r : Fin (N + 1)) : E.dmap z v r = E.djac z r v := by
  simp only [dmap, ContinuousLinearMap.pi_apply]

@[simp] theorem dpsi_apply (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (v : Fin (N + 1) → ℝ) (i : Fin N) : E.dpsi z v i = E.djac z (E.lastRow.succAbove i) v := by
  simp only [dpsi, ContinuousLinearMap.pi_apply]

@[simp] theorem dgLast_apply (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (v : Fin (N + 1) → ℝ) : E.dgLast z v = E.djac z E.lastRow v := rfl

@[simp] theorem dG_apply (E : ETData N (rt + 1) n re) (x : Fin N → ℝ) (v : Fin N → ℝ) :
    E.dG x v = E.dpsi (E.chart x) (E.dchart x v) := rfl

end ETData

end Work.WilE3K
