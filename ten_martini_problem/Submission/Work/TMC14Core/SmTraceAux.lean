/-
# TMC14Core: change-of-basis infrastructure for `smMat_trace`

This file provides the transfer-matrix bookkeeping used to compute the determinant of the
"shooting" matrix `smMat`.  The key object is the matrix `TMat n d` whose columns are the
two solutions of the recurrence `Rec_i = u_{i-1} - d_i u_i + u_{i+1} = 0` with initial data
`(u_{-1}, u_0) = (1,0)` and `(0,1)`, together with the impulse responses for the
inhomogeneous problem.  Multiplying `smMat` on the right by `TMat` puts it in block form,
from which its determinant is read off.
-/
import Mathlib
import Submission.Work.TMC14Core.cycSetup

open LeanEval.Analysis.TenMartini
noncomputable section

set_option linter.unusedSimpArgs false

namespace Work.TMC14Core.SmTrace

open Matrix

/-! ## The transfer matrix and its entries -/

/-- `tm2 a * B` computed entrywise. -/
lemma tm2_mul_eq (a : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    tm2 a * B = !![a * B 0 0 - B 1 0, a * B 0 1 - B 1 1; B 0 0, B 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tm2, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

lemma transProd_succ_00 (d : ℕ → ℂ) (k : ℕ) :
    (transProd d (k+1)) 0 0 = d k * (transProd d k) 0 0 - (transProd d k) 1 0 := by
  rw [transProd_succ, tm2_mul_eq]; simp

lemma transProd_succ_01 (d : ℕ → ℂ) (k : ℕ) :
    (transProd d (k+1)) 0 1 = d k * (transProd d k) 0 1 - (transProd d k) 1 1 := by
  rw [transProd_succ, tm2_mul_eq]; simp

lemma transProd_succ_10 (d : ℕ → ℂ) (k : ℕ) :
    (transProd d (k+1)) 1 0 = (transProd d k) 0 0 := by
  rw [transProd_succ, tm2_mul_eq]; simp

lemma transProd_succ_11 (d : ℕ → ℂ) (k : ℕ) :
    (transProd d (k+1)) 1 1 = (transProd d k) 0 1 := by
  rw [transProd_succ, tm2_mul_eq]; simp

/-- The three-term recurrence for the `(1,1)` entry. -/
lemma transProd_rec_11 (d : ℕ → ℂ) (i : ℕ) :
    (transProd d (i+2)) 1 1 = d i * (transProd d (i+1)) 1 1 - (transProd d i) 1 1 := by
  rw [transProd_succ_11 d (i+1), transProd_succ_01 d i, ← transProd_succ_11 d i]

/-- The three-term recurrence for the `(1,0)` entry. -/
lemma transProd_rec_10 (d : ℕ → ℂ) (i : ℕ) :
    (transProd d (i+2)) 1 0 = d i * (transProd d (i+1)) 1 0 - (transProd d i) 1 0 := by
  rw [transProd_succ_10 d (i+1), transProd_succ_00 d i, ← transProd_succ_10 d i]

/-- The transfer product is unimodular. -/
lemma transProd_det (d : ℕ → ℂ) (k : ℕ) : (transProd d k).det = 1 := by
  induction k with
  | zero => simp [transProd]
  | succ j ih =>
    rw [transProd_succ, Matrix.det_mul, ih, mul_one]
    simp [tm2, Matrix.det_fin_two]

lemma transProd_one (d : ℕ → ℂ) : transProd d 1 = tm2 (d 0) := by
  rw [transProd_succ d 0, transProd_zero, mul_one]

/-! ## Products over a range of indices -/

/-- `subProd d b m = tm2 (d (b+m-1)) ⋯ tm2 (d b)` (`m` factors, `1` if `m = 0`). -/
def subProd (d : ℕ → ℂ) (b : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | (m+1) => tm2 (d (b+m)) * subProd d b m

lemma subProd_zero (d : ℕ → ℂ) (b : ℕ) : subProd d b 0 = 1 := rfl

lemma subProd_succ (d : ℕ → ℂ) (b m : ℕ) :
    subProd d b (m+1) = tm2 (d (b+m)) * subProd d b m := rfl

lemma subProd_succ_00 (d : ℕ → ℂ) (b m : ℕ) :
    (subProd d b (m+1)) 0 0 = d (b+m) * (subProd d b m) 0 0 - (subProd d b m) 1 0 := by
  rw [subProd_succ, tm2_mul_eq]; simp

lemma subProd_succ_10 (d : ℕ → ℂ) (b m : ℕ) :
    (subProd d b (m+1)) 1 0 = (subProd d b m) 0 0 := by
  rw [subProd_succ, tm2_mul_eq]; simp

/-- The three-term recurrence for `subProd`, in the form used for the impulse responses. -/
lemma subProd_rec_10 (d : ℕ → ℂ) (b j : ℕ) :
    (subProd d b (j+2)) 1 0 = d (b+j) * (subProd d b (j+1)) 1 0 - (subProd d b j) 1 0 := by
  have h1 : (subProd d b (j+2)) 1 0 = (subProd d b (j+1)) 0 0 := by
    have := subProd_succ_10 d b (j+1); simpa using this
  rw [h1, subProd_succ_00]
  have h2 : (subProd d b j) 0 0 = (subProd d b (j+1)) 1 0 := by
    have := subProd_succ_10 d b j; simpa using this.symm
  rw [h2]

lemma subProd_one (d : ℕ → ℂ) (b : ℕ) : subProd d b 1 = tm2 (d b) := by
  rw [subProd_succ d b 0, subProd_zero, mul_one]; simp

/-! ## The change-of-basis matrix -/

/-- `TMat n d` has columns indexed by the unknowns `u_{-1}, u_0, …, u_n`: column `0` is the
recurrence solution with `(u_{-1},u_0) = (1,0)`, column `1` that with `(0,1)`, and column
`j ≥ 2` is the impulse response with `u_{j-2} = 0`, `u_{j-1} = 1` and `Rec_i = δ_{i,j-2}`. -/
def TMat (n : ℕ) (d : ℕ → ℂ) : Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
  Matrix.of fun i j =>
    if j.val = 0 then (transProd d i.val) 1 1
    else if j.val = 1 then (transProd d i.val) 1 0
    else if i.val < j.val then 0
    else (subProd d (j.val - 1) (i.val - (j.val - 1))) 1 0

lemma TMat_col_zero (n : ℕ) (d : ℕ → ℂ) (i : Fin (n+2)) :
    TMat n d i (0 : Fin (n+2)) = (transProd d i.val) 1 1 := by
  simp [TMat]

lemma TMat_col_one (n : ℕ) (d : ℕ → ℂ) (i : Fin (n+2)) :
    TMat n d i (1 : Fin (n+2)) = (transProd d i.val) 1 0 := by
  simp [TMat]

lemma TMat_col_ge_two (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (hj : 2 ≤ j.val) (i : Fin (n+2)) :
    TMat n d i j = if i.val < j.val then 0 else (subProd d (j.val-1) (i.val-(j.val-1))) 1 0 := by
  have h0 : ¬ (j.val = 0) := by omega
  have h1 : ¬ (j.val = 1) := by omega
  rw [TMat, Matrix.of_apply, if_neg h0, if_neg h1]

lemma TMat_col_ge_two_of (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (hj : 2 ≤ j.val)
    (i : Fin (n+2)) (hi : j.val - 1 ≤ i.val) :
    TMat n d i j = (subProd d (j.val-1) (i.val-(j.val-1))) 1 0 := by
  rw [TMat_col_ge_two n d j hj i]
  rcases Nat.lt_or_ge i.val j.val with h | h
  · have hz : i.val - (j.val - 1) = 0 := by omega
    rw [if_pos h, hz, subProd_zero]
    simp
  · rw [if_neg (by omega)]

lemma TMat_apply_of_lt (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (hj : 2 ≤ j.val)
    (i : Fin (n+2)) (hi : i.val < j.val) : TMat n d i j = 0 := by
  rw [TMat_col_ge_two n d j hj i, if_pos hi]

lemma TMat_diag_col (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (hj : 2 ≤ j.val) :
    TMat n d j j = 1 := by
  rw [TMat_col_ge_two_of n d j hj j (by omega)]
  have h : j.val - (j.val - 1) = 1 := by omega
  rw [h, subProd_one]; simp [tm2]

/-- The recurrence relation satisfied by the impulse response (case `j ≥ 2`). -/
lemma TMat_rec_col_ge_two (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (hj : 2 ≤ j.val)
    (i : ℕ) (hi : i + 2 < n + 2) (hk : j.val ≤ i + 1) :
    TMat n d ⟨i, by omega⟩ j - d i * TMat n d ⟨i+1, by omega⟩ j + TMat n d ⟨i+2, hi⟩ j = 0 := by
  rw [TMat_col_ge_two_of n d j hj ⟨i, by omega⟩ (by simp; omega),
      TMat_col_ge_two_of n d j hj ⟨i+1, by omega⟩ (by simp; omega),
      TMat_col_ge_two_of n d j hj ⟨i+2, hi⟩ (by simp; omega)]
  have h1 : (i+1) - (j.val-1) = (i - (j.val-1)) + 1 := by omega
  have h2 : (i+2) - (j.val-1) = (i - (j.val-1)) + 2 := by omega
  have h3 : j.val - 1 + (i - (j.val-1)) = i := by omega
  rw [h1, h2, subProd_rec_10 d (j.val-1) (i - (j.val-1)), h3]
  ring

/-- **The key computation**: the recurrence residual `Rec_i` evaluated on column `j` of
`TMat` is `1` exactly when `j = i+2` and `0` otherwise.  This holds for all `j`. -/
lemma TMat_col_rec (n : ℕ) (d : ℕ → ℂ) (j : Fin (n+2)) (i : ℕ) (hi : i + 2 < n + 2) :
    TMat n d ⟨i, by omega⟩ j - d i * TMat n d ⟨i+1, by omega⟩ j + TMat n d ⟨i+2, hi⟩ j
      = if j.val = i + 2 then 1 else 0 := by
  by_cases hj : j.val ≤ 1
  · have hj01 : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj01 with hjv | hjv
    · have hj0 : j = 0 := Fin.ext (by simpa using hjv)
      rw [hj0, TMat_col_zero, TMat_col_zero, TMat_col_zero, transProd_rec_11 d i]
      rw [if_neg (by simp : ¬ ((0 : Fin (n+2)).val = i + 2))]
      ring
    · have hj1 : j = 1 := Fin.ext (by simpa using hjv)
      rw [hj1, TMat_col_one, TMat_col_one, TMat_col_one, transProd_rec_10 d i]
      rw [if_neg (by simp : ¬ ((1 : Fin (n+2)).val = i + 2))]
      ring
  · have hj2 : 2 ≤ j.val := by omega
    by_cases hc : j.val ≤ i + 1
    · rw [TMat_rec_col_ge_two n d j hj2 i hi hc, if_neg (by omega)]
    · by_cases hc2 : j.val = i + 2
      · have hji : TMat n d (⟨i, by omega⟩ : Fin (n+2)) j = 0 :=
          TMat_apply_of_lt n d j hj2 _ (by simp; omega)
        have hji1 : TMat n d (⟨i+1, by omega⟩ : Fin (n+2)) j = 0 :=
          TMat_apply_of_lt n d j hj2 _ (by simp; omega)
        have hji2 : TMat n d ⟨i+2, hi⟩ j = 1 := by
          have hje : (⟨i+2, hi⟩ : Fin (n+2)) = j := Fin.ext (by simp [hc2])
          rw [hje, TMat_diag_col n d j hj2]
        rw [hji, hji1, hji2, if_pos hc2]
        ring
      · have hgt : i + 2 < j.val := by omega
        have hji : TMat n d (⟨i, by omega⟩ : Fin (n+2)) j = 0 :=
          TMat_apply_of_lt n d j hj2 _ (by simp; omega)
        have hji1 : TMat n d (⟨i+1, by omega⟩ : Fin (n+2)) j = 0 :=
          TMat_apply_of_lt n d j hj2 _ (by simp; omega)
        have hji2 : TMat n d ⟨i+2, hi⟩ j = 0 := TMat_apply_of_lt n d j hj2 _ hgt
        rw [hji, hji1, hji2, if_neg (by omega)]
        ring

/-! ## `TMat` is lower triangular with unit diagonal, hence has determinant `1` -/

lemma TMat_diag (n : ℕ) (d : ℕ → ℂ) (i : Fin (n+2)) : TMat n d i i = 1 := by
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext (by simpa using h)
    rw [hi, TMat_col_zero]
    simp
  · by_cases h1 : i.val = 1
    · have hi : i = 1 := Fin.ext (by simpa using h1)
      have hv : ((1 : Fin (n+2)) : ℕ) = 1 := Fin.val_one _
      rw [hi, TMat_col_one, hv, transProd_one]
      simp [tm2]
    · exact TMat_diag_col n d i (by omega)

lemma TMat_det (n : ℕ) (d : ℕ → ℂ) : (TMat n d).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular (TMat n d)]
  · simp [TMat_diag]
  · intro i j hij
    have hval : i.val < j.val := hij
    rw [TMat, Matrix.of_apply]
    by_cases h0 : j.val = 0
    · omega
    by_cases h1 : j.val = 1
    · rw [if_neg (by omega), if_pos h1]
      have hi : i.val = 0 := by omega
      rw [hi]
      simp [transProd]
    · rw [if_neg (by omega), if_neg h1, if_pos hval]

/-! ## Determinants of matrices whose bottom rows are standard basis vectors -/

/-- If every row of index `≥ 2` is the corresponding standard basis vector, the determinant
is the determinant of the top left `2 × 2` block. -/
lemma det_eq_topleft_of (N : ℕ) (A : Matrix (Fin (N+2)) (Fin (N+2)) ℂ)
    (h : ∀ i j : Fin (N+2), 2 ≤ i.val → A i j = if i = j then 1 else 0) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  have hzero : ∀ i : Fin (N+2), ¬ (i.val < 2) → ∀ j : Fin (N+2), j.val < 2 → A i j = 0 := by
    intro i hi j hj
    rw [h i j (by omega)]
    by_cases he : i = j
    · subst he; omega
    · simp [he]
  have hbr : A.toSquareBlockProp (fun i : Fin (N+2) => ¬ i.val < 2) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show A ↑i ↑j = if i = j then (1:ℂ) else 0
    rw [h (↑i) (↑j) (by omega)]
    congr 1
    exact propext ⟨fun hh => Subtype.ext hh, fun hh => by rw [hh]⟩
  rw [Matrix.twoBlockTriangular_det A (fun i : Fin (N+2) => i.val < 2) hzero, hbr,
    Matrix.det_one, mul_one]
  let e : Fin 2 ≃ {i : Fin (N+2) // i.val < 2} :=
    { toFun := fun k => ⟨⟨k.val, Nat.lt_of_lt_of_le k.isLt (by omega)⟩, k.isLt⟩
      invFun := fun i => ⟨i.val, i.property⟩
      left_inv := by intro k; rfl
      right_inv := by intro i; rfl }
  rw [← Matrix.det_submatrix_equiv_self e (A.toSquareBlockProp fun i : Fin (N+2) => i.val < 2)]
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  show A ↑(e 0) ↑(e 0) * A ↑(e 1) ↑(e 1) - A ↑(e 0) ↑(e 1) * A ↑(e 1) ↑(e 0)
      = A 0 0 * A 1 1 - A 0 1 * A 1 0
  rfl

end Work.TMC14Core.SmTrace
