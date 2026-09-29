import Mathlib
import Submission.Work.TMComp.IDSDefs

/-!
# The box characteristic polynomial is the Jacobi continuant

`Jbox α lam θ n` is the `n × n` real-symmetric tridiagonal (Dirichlet) box matrix with
diagonal `pot α lam θ j = 2λ cos(2π(θ+jα))` and off-diagonal `1`.  `jacPoly α lam θ n` is
the polynomial defined by the three-term (continuant) recursion
`P_{n+1} = (X - v_n) P_n - P_{n-1}`, `P_0 = 1`, `P_{-1} = 0`.

This file proves `charpoly (Jbox) = (jacPoly).map (algebraMap ℝ ℂ)`, together with the
monicity and degree of `jacPoly`.

The main ingredient is the classical fact that the determinant of a tridiagonal matrix
satisfies the same three-term recursion (`det_bandMat_succ`), proved here from the
Laplace expansion along the last row/column.
-/

noncomputable section

open Polynomial Matrix Finset

namespace Work.TMComp.IDSBox

open Work.TMComp

/-! ## General tridiagonal (band) matrices -/

/-- `bandMat c d n` is the `n × n` tridiagonal matrix with diagonal `d 0, …, d (n-1)` and
constant off-diagonal entries `c`. -/
def bandMat {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if i = j then d (i : ℕ)
    else if ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) then c else 0

/-- Removing the last row and column of a band matrix leaves the smaller band matrix. -/
lemma bandMat_sub_last {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (m : ℕ) :
    (bandMat c d (m+1)).submatrix (Fin.last m).succAbove (Fin.last m).succAbove
      = bandMat c d m := by
  ext i j
  simp [bandMat, Matrix.submatrix, Fin.succAbove]

/-- The embedding of `Fin n` into `Fin (n+2)` skipping `n` and inserting `n+1`. -/
lemma col_succ (n : ℕ) (j : Fin n) :
    ((Fin.last n).castSucc : Fin (n+2)).succAbove j.castSucc = j.castSucc.castSucc := by
  rw [Fin.succAbove_castSucc_of_lt]; exact Fin.castSucc_lt_last j

/-- The "skew" principal minor obtained by deleting the last row and the second-to-last
column of a band matrix reduces, after deleting one more row and column, to the band
matrix of size `n`. -/
lemma bandMat_sub_last2 {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    ((bandMat c d (n+2)).submatrix (Fin.last (n+1)).succAbove
        ((Fin.last n).castSucc).succAbove).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove = bandMat c d n := by
  ext i j
  simp only [Matrix.submatrix_apply, bandMat, Matrix.of_apply]
  rw [Fin.succAbove_last, Fin.succAbove_last, col_succ]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]

/-- The last row of a band matrix vanishes away from the last two columns. -/
lemma bandMat_entry_last_ne {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ)
    (b' : Fin (n+2)) (h1 : b' ≠ Fin.last (n+1)) (h2 : b' ≠ (Fin.last n).castSucc) :
    bandMat c d (n+2) (Fin.last (n+1)) b' = 0 := by
  simp only [bandMat, Matrix.of_apply]
  split_ifs with hd hc
  · exact absurd hd.symm h1
  · exfalso
    rcases hc with hc | hc
    · simp only [Fin.val_last] at hc; omega
    · apply h2; apply Fin.ext
      simp only [Fin.val_last, Fin.val_castSucc] at hc ⊢; omega
  · rfl

/-- The column index of the second-to-last column after reindexing is the last column. -/
lemma col_last (n : ℕ) :
    ((Fin.last n).castSucc : Fin (n+2)).succAbove (Fin.last n) = Fin.last (n+1) := by
  rw [Fin.succAbove_castSucc_self]; rfl

/-- Column entries of the "skew" minor vanish except in the last row. -/
lemma bandMat_entry_col {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ)
    (i : Fin (n+1)) (h : i ≠ Fin.last n) :
    bandMat c d (n+2) i.castSucc (Fin.last (n+1)) = 0 := by
  simp only [bandMat, Matrix.of_apply]
  split_ifs with hd hc
  · exfalso
    rw [Fin.ext_iff] at hd
    simp only [Fin.val_last, Fin.val_castSucc] at hd
    omega
  · exfalso
    rcases hc with hc | hc
    · apply h; apply Fin.ext; simp only [Fin.val_last, Fin.val_castSucc] at hc ⊢; omega
    · simp only [Fin.val_last, Fin.val_castSucc] at hc; omega
  · rfl

/-- The last diagonal entry of a band matrix. -/
lemma bandMat_entry_diag {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    bandMat c d (n+2) (Fin.last (n+1)) (Fin.last (n+1)) = d (n+1) := by
  simp [bandMat]

/-- The `(last, last-1)` entry of a band matrix is the off-diagonal constant. -/
lemma bandMat_entry_sub {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    bandMat c d (n+2) (Fin.last (n+1)) ((Fin.last n).castSucc) = c := by
  simp only [bandMat, Matrix.of_apply]
  rw [if_neg (by simp [Fin.ext_iff])]
  rw [if_pos (by right; simp [Fin.val_last, Fin.val_castSucc])]

/-- The transposed `(last-1, last)` entry of a band matrix is the off-diagonal constant. -/
lemma bandMat_entry_sub' {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    bandMat c d (n+2) ((Fin.last n).castSucc) (Fin.last (n+1)) = c := by
  simp only [bandMat, Matrix.of_apply]
  rw [if_neg (by simp [Fin.ext_iff])]
  rw [if_pos (by left; simp [Fin.val_last, Fin.val_castSucc])]

/-- **Continuant recurrence for tridiagonal determinants.** The determinant of the
`(n+2) × (n+2)` band matrix with diagonal `d` and off-diagonal `c` satisfies
`D_{n+2} = d_{n+1} D_{n+1} - c² D_n`. -/
theorem det_bandMat_succ {R : Type*} [CommRing R] (c : R) (d : ℕ → R) (n : ℕ) :
    (bandMat c d (n+2)).det = d (n+1) * (bandMat c d (n+1)).det - c^2 * (bandMat c d n).det := by
  have hab : (Fin.last (n+1) : Fin (n+2)) ≠ (Fin.last n).castSucc := by
    simp [Fin.ext_iff]
  -- determinant of the "skew" minor (delete last row and second-to-last column)
  have hBc : ((bandMat c d (n+2)).submatrix (Fin.last (n+1)).succAbove
        ((Fin.last n).castSucc).succAbove).det = c * (bandMat c d n).det := by
    rw [Matrix.det_succ_column _ (Fin.last n)]
    rw [Finset.sum_eq_single (Fin.last n)]
    · rw [bandMat_sub_last2]
      rw [show (bandMat c d (n+2)).submatrix (Fin.last (n+1)).succAbove
            ((Fin.last n).castSucc).succAbove (Fin.last n) (Fin.last n) = c by
        rw [Matrix.submatrix_apply, Fin.succAbove_last, col_last, bandMat_entry_sub']]
      rw [show (-1:R)^((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 by
        rw [show (Fin.last n : ℕ) + (Fin.last n : ℕ) = 2 * n by simp; ring, pow_mul]; norm_num]
      ring
    · intro b' _ hb'
      rw [show (bandMat c d (n+2)).submatrix (Fin.last (n+1)).succAbove
            ((Fin.last n).castSucc).succAbove b' (Fin.last n) = 0 by
        rw [Matrix.submatrix_apply, Fin.succAbove_last, col_last]
        exact bandMat_entry_col (R := R) c d n b' hb']
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- all remaining terms of the last-row expansion vanish
  have hzero : ∀ b' ∈ (Finset.univ : Finset (Fin (n+2))),
      b' ≠ Fin.last (n+1) ∧ b' ≠ (Fin.last n).castSucc →
      (-1) ^ ((Fin.last (n+1) : ℕ) + (b' : ℕ)) * bandMat c d (n+2) (Fin.last (n+1)) b' *
        ((bandMat c d (n+2)).submatrix (Fin.last (n+1)).succAbove b'.succAbove).det = 0 := by
    intro b' _ h
    rw [bandMat_entry_last_ne (R := R) c d n b' h.1 h.2]; ring
  rw [Matrix.det_succ_row (bandMat c d (n+2)) (Fin.last (n+1))]
  rw [Finset.sum_eq_add (Fin.last (n+1)) ((Fin.last n).castSucc) hab hzero
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
  rw [bandMat_sub_last c d (n+1), hBc]
  rw [show (-1:R)^((Fin.last (n+1) : ℕ) + (Fin.last (n+1) : ℕ)) = 1 by
    rw [show (Fin.last (n+1) : ℕ) + (Fin.last (n+1) : ℕ) = 2 * (n+1) by simp; ring, pow_mul]
    norm_num]
  rw [show (-1:R)^((Fin.last (n+1) : ℕ) + ((Fin.last n).castSucc : ℕ)) = -1 by
    rw [show (Fin.last (n+1) : ℕ) + ((Fin.last n).castSucc : ℕ) = 2 * n + 1 by
        simp only [Fin.val_last, Fin.val_castSucc]; ring, pow_succ, pow_mul]; norm_num]
  rw [bandMat_entry_diag, bandMat_entry_sub]
  ring

/-! ## The continuant polynomial -/

/-- Auxiliary pair recursion for the continuant polynomials. -/
def contPair {R : Type*} [CommRing R] (w : ℕ → R) : ℕ → Polynomial R × Polynomial R
  | 0 => (1, 0)
  | n+1 => ((X - C (w n)) * (contPair w n).1 - (contPair w n).2, (contPair w n).1)

/-- The continuant polynomial of the sequence `w`: `P_0 = 1`,
`P_{n+1} = (X - w_n) P_n - P_{n-1}`. -/
def contPoly {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ) : Polynomial R := (contPair w n).1

/-- The two-step recurrence satisfied by the continuant polynomial. -/
lemma contPoly_succ_succ {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ) :
    contPoly w (n+2) = (X - C (w (n+1))) * contPoly w (n+1) - contPoly w n := by
  simp [contPoly, contPair]

/-- The characteristic matrix of a band matrix with off-diagonal `1` is the band matrix
with diagonal `X - w_i` and off-diagonal `-1`. -/
lemma charmatrix_bandMat {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ) :
    charmatrix (bandMat (1:R) w n) = bandMat (-1) (fun i => (X : R[X]) - C (w i)) n := by
  ext i j
  rw [Matrix.charmatrix_apply, bandMat, bandMat, Matrix.of_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · simp only [h, ↓reduceIte]
    by_cases hc : ((i:ℕ)+1 = (j:ℕ) ∨ (j:ℕ)+1 = (i:ℕ)) <;> simp [h, hc]

/-- **Characteristic polynomial of the band matrix is the continuant.** -/
theorem charpoly_bandMat {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ) :
    (bandMat (1:R) w n).charpoly = contPoly w n := by
  have hD : ∀ k, (bandMat (1:R) w k).charpoly
      = (bandMat (-1) (fun i => (X : R[X]) - C (w i)) k).det := by
    intro k
    rw [Matrix.charpoly, charmatrix_bandMat]
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.charpoly, bandMat, contPoly, contPair]
  | one => simp [Matrix.charpoly, bandMat, contPoly, contPair]
  | more n ih ih' =>
    rw [hD (n+2), det_bandMat_succ, ← hD (n+1), ← hD n, ih', ih]
    have h1 : ((-1 : R[X])^2) = 1 := by norm_num
    rw [h1, one_mul, ← contPoly_succ_succ w n]

/-! ## From the continuant to `jacPoly` -/

/-- The pair recursion defining `jacPair` agrees with `contPair` applied to the potential. -/
lemma jacPair_eq_contPair (α lam θ : ℝ) : ∀ n,
    jacPair α lam θ n = contPair (fun k => pot α lam θ k) n
  | 0 => rfl
  | n+1 => by simp [jacPair, contPair, jacPair_eq_contPair α lam θ n]

/-- `jacPoly` is the continuant of the potential sequence. -/
lemma jacPoly_eq_contPoly (α lam θ : ℝ) (n : ℕ) :
    jacPoly α lam θ n = contPoly (fun k => pot α lam θ k) n := by
  simp only [jacPoly, contPoly, jacPair_eq_contPair]

/-- The box matrix is the (real) band matrix mapped into `ℂ`. -/
theorem Jbox_eq (α lam θ : ℝ) (n : ℕ) :
    Jbox α lam θ n = (bandMat (1:ℝ) (fun k => pot α lam θ k) n).map (algebraMap ℝ ℂ) := by
  ext i j
  simp only [Jbox, Matrix.map_apply, bandMat, Matrix.of_apply]
  split_ifs <;> simp [Complex.coe_algebraMap]

/-! ## The main statement -/

theorem charpoly (α lam θ : ℝ) (n : ℕ) :
    (Work.TMComp.Jbox α lam θ n).charpoly
        = (Work.TMComp.jacPoly α lam θ n).map (algebraMap ℝ ℂ) ∧
      (Work.TMComp.jacPoly α lam θ n).Monic ∧
      (Work.TMComp.jacPoly α lam θ n).natDegree = n := by
  have hf : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
  have h1 : (Jbox α lam θ n).charpoly = (jacPoly α lam θ n).map (algebraMap ℝ ℂ) := by
    rw [Jbox_eq, Matrix.charpoly_map, charpoly_bandMat, jacPoly_eq_contPoly]
  refine ⟨h1, ?_, ?_⟩
  · exact (Function.Injective.monic_map_iff hf).mpr (h1 ▸ Matrix.charpoly_monic _)
  · have h3 : ((jacPoly α lam θ n).map (algebraMap ℝ ℂ)).natDegree = n := by
      rw [← h1, Matrix.charpoly_natDegree_eq_dim]
      simp
    rwa [natDegree_map_eq_of_injective hf] at h3

end Work.TMComp.IDSBox
