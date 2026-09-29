/-
# Setup for the Chebyshev (polynomial-in-`cos`) form of the Dirichlet continuant

This file collects the definitions and the elementary "continuant = `(0,0)` entry of a
transfer-matrix product" machinery used by `Work.TMC16Core.Basic.pd_cheb`.

The continuant `cont l` of a list of ring elements is the `(0,0)`-entry of the ordered
product of the `2×2` transfer matrices `!![b, -1; 1, 0]`.  Its key property is invariance
under reversal of the list, proved by conjugating with `diag(1,-1)` (which turns each
transfer matrix into its transpose).
-/
import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Cheb

open Matrix Polynomial

noncomputable section

/-! ## 1. Continuants -/

/-- The `2×2` transfer matrix with off-diagonals `-1`, `1`. -/
def Bm {R : Type*} [CommRing R] (b : R) : Matrix (Fin 2) (Fin 2) R := !![b, -1; 1, 0]

/-- `diag(1,-1)`.  It conjugates `Bm b` into its transpose. -/
def Dm {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else -1)

/-- Ordered product of transfer matrices: `mL [b₀, b₁, … , b_{n-1}] = Bm b₀ * ⋯ * Bm b_{n-1}`. -/
def mL {R : Type*} [CommRing R] : List R → Matrix (Fin 2) (Fin 2) R
  | [] => 1
  | b :: l => Bm b * mL l

/-- The continuant of a list, as the `(0,0)`-entry of the transfer-matrix product. -/
def cont {R : Type*} [CommRing R] (l : List R) : R := (mL l) 0 0

lemma Dm_mul_Dm {R : Type*} [CommRing R] : (Dm : Matrix (Fin 2) (Fin 2) R) * Dm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Dm, Matrix.mul_apply, Matrix.diagonal_apply]

lemma transpose_Bm {R : Type*} [CommRing R] (b : R) :
    (Bm b).transpose = Dm * Bm b * Dm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Bm, Dm, Matrix.mul_apply, Matrix.diagonal_apply]

lemma mL_singleton {R : Type*} [CommRing R] (b : R) : mL [b] = Bm b := by simp [mL]

lemma mL_append {R : Type*} [CommRing R] (l₁ l₂ : List R) :
    mL (l₁ ++ l₂) = mL l₁ * mL l₂ := by
  induction l₁ with
  | nil => simp [mL]
  | cons b l ih => simp [mL, ih, mul_assoc]

lemma key {R : Type*} [CommRing R] (M N : Matrix (Fin 2) (Fin 2) R) :
    Dm * M * Dm * (Dm * N * Dm) = Dm * (M * N) * Dm := by
  rw [show Dm * M * Dm * (Dm * N * Dm) = Dm * M * (Dm * Dm) * N * Dm from by noncomm_ring,
    Dm_mul_Dm, mul_one]
  noncomm_ring

lemma transpose_mL {R : Type*} [CommRing R] (l : List R) :
    (mL l).transpose = Dm * mL l.reverse * Dm := by
  induction l with
  | nil => rw [mL, Matrix.transpose_one, List.reverse_nil, mL, mul_one]; exact Dm_mul_Dm.symm
  | cons b l ih =>
    rw [mL, Matrix.transpose_mul, ih, transpose_Bm, key, ← mL_singleton, ← mL_append,
      List.reverse_cons]

lemma Dm_conj {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (Dm * M * Dm : Matrix (Fin 2) (Fin 2) R) =
      Matrix.of ![![M 0 0, -(M 0 1)], ![-(M 1 0), M 1 1]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dm, Matrix.mul_apply, Matrix.diagonal_apply]

lemma Dm_conj_00 {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (Dm * M * Dm : Matrix (Fin 2) (Fin 2) R) 0 0 = M 0 0 := by
  rw [Dm_conj]; simp

lemma cont_nil {R : Type*} [CommRing R] : cont ([] : List R) = 1 := rfl

lemma cont_succ {R : Type*} [CommRing R] (b : R) (l : List R) :
    (mL (b :: l)) 0 0 = b * (mL l) 0 0 - (mL l) 1 0 := by
  simp only [mL]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Bm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma mL_row1 {R : Type*} [CommRing R] (c : R) (l : List R) :
    (mL (c :: l)) 1 0 = (mL l) 0 0 := by
  simp only [mL]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Bm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma cont_singleton {R : Type*} [CommRing R] (b : R) : cont [b] = b := by
  simp only [cont, mL, Matrix.mul_one, Bm, Matrix.of_apply, Matrix.cons_val_zero]

lemma cont_cons_cons {R : Type*} [CommRing R] (b c : R) (l : List R) :
    cont (b :: c :: l) = b * cont (c :: l) - cont l := by
  simp only [cont]
  rw [cont_succ b (c :: l), mL_row1 c l]

lemma cont_reverse {R : Type*} [CommRing R] (l : List R) : cont l.reverse = cont l := by
  simp only [cont]
  rw [← Dm_conj_00 (mL l.reverse), ← transpose_mL, Matrix.transpose_apply]

lemma mL_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : List R) :
    mL (l.map φ) = (mL l).map φ := by
  induction l with
  | nil => simp [mL, Matrix.map_one]
  | cons b l ih =>
    rw [List.map_cons, mL, mL, ih, Matrix.map_mul,
      show (Bm b).map (⇑φ) = Bm (φ b) from by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Bm]]

lemma cont_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : List R) :
    cont (l.map φ) = φ (cont l) := by
  simp only [cont, mL_map, Matrix.map_apply]

/-! ## 2. The bivariate polynomial encoding -/

/-- The `cos(2πx)` variable as an element of `ℂ[X][X]`. -/
def cX : Polynomial (Polynomial ℂ) := Polynomial.C Polynomial.X

/-- The `sin(2πx)` variable as an element of `ℂ[X][X]`. -/
def sY : Polynomial (Polynomial ℂ) := Polynomial.X

/-- A complex constant, as an element of `ℂ[X][X]`. -/
def cst (z : ℂ) : Polynomial (Polynomial ℂ) := Polynomial.C (Polynomial.C z)

/-- Total-degree bound for the bivariate polynomial ring `ℂ[X][X]`: the coefficient of
`Y^i` has `X`-degree at most `d - i`. -/
def DegLe (P : Polynomial (Polynomial ℂ)) (d : ℕ) : Prop :=
  ∀ i, i ≤ P.natDegree → (P.coeff i).natDegree + i ≤ d

/-- The centre `((k-1)/2)·α` of the length-`k` window. -/
def ctr (k : ℕ) (α : ℝ) : ℝ := (((k : ℝ) - 1) / 2) * α

/-- The `j`-th potential `E - 2λ cos(2π(x + jα - centre))` written as an element of
`ℂ[X][X]` with `X = cos 2πx` and `Y = sin 2πx`. -/
def afun (α lam : ℝ) (E : ℂ) (k : ℕ) (j : ℕ) : Polynomial (Polynomial ℂ) :=
  cst E - cst ((2 * lam : ℝ) : ℂ) *
    (cst (Real.cos (2 * Real.pi * ((j : ℝ) * α - ctr k α))) * cX
      - cst (Real.sin (2 * Real.pi * ((j : ℝ) * α - ctr k α))) * sY)

/-- The list of potentials for the length-`k` window, indexed `0, …, k-1`. -/
def listA (α lam : ℝ) (E : ℂ) (k : ℕ) : List (Polynomial (Polynomial ℂ)) :=
  (List.range k).map (afun α lam E k)

/-- The bivariate polynomial representing the continuant `P_k(θ)` at the centred phase,
with `X = cos 2πx`, `Y = sin 2πx`. -/
def Pbiv (α lam : ℝ) (E : ℂ) (k : ℕ) : Polynomial (Polynomial ℂ) :=
  cont (listA α lam E k)

end

end Work.TMC16Core.Cheb
