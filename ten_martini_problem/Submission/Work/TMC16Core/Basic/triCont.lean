/-
# Tridiagonal (Jacobi) determinants and continuants

Ingredients for the Cramér-rule form of the Dirichlet Green's function of the almost
Mathieu operator (`cramer.lean`).

For a sequence `a : ℕ → ℂ` we define the continuant `cont a n` by
`cont a 0 = 1`, `cont a 1 = a 0`, `cont a (n+2) = a (n+1) * cont a (n+1) - cont a n`, and
the `n × n` tridiagonal matrix `triD d n` with diagonal `d` and off-diagonal `1`.

Main results:

* `det_triD : (triD d n).det = cont d n`,
* `pd_eq_cont : pd α lam θ E (n+1) = cont (fun i => E - amoPot α lam θ i) n`,
* the determinant of a square matrix whose first row (resp. last row) is a standard basis
  vector, the tool used to evaluate the minors of `triD` recursively.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs

noncomputable section

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-! ## Continuants -/

/-- The continuant of a sequence: `cont a 0 = 1`, `cont a 1 = a 0`,
`cont a (n+2) = a (n+1) * cont a (n+1) - cont a n`. -/
def cont (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a 0
  | n + 2 => a (n + 1) * cont a (n + 1) - cont a n

@[simp] theorem cont_zero (a : ℕ → ℂ) : cont a 0 = 1 := rfl
@[simp] theorem cont_one (a : ℕ → ℂ) : cont a 1 = a 0 := rfl

theorem cont_succ_succ (a : ℕ → ℂ) (n : ℕ) :
    cont a (n + 2) = a (n + 1) * cont a (n + 1) - cont a n := rfl

/-- Shift of a sequence by `c`. -/
def seqShift (a : ℕ → ℂ) (c : ℕ) : ℕ → ℂ := fun i => a (i + c)

@[simp] theorem seqShift_apply (a : ℕ → ℂ) (c i : ℕ) : seqShift a c i = a (i + c) := rfl

theorem seqShift_seqShift (a : ℕ → ℂ) (c₁ c₂ : ℕ) :
    seqShift (seqShift a c₁) c₂ = seqShift a (c₁ + c₂) := by
  funext i
  simp only [seqShift_apply]
  congr 1
  omega

theorem cont_neg (a : ℕ → ℂ) (n : ℕ) :
    cont (fun i => -a i) n = (-1) ^ n * cont a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      rw [cont_succ_succ, ih1, ih2, cont_succ_succ]
      have h2 : (-1 : ℂ) ^ (n + 2) = (-1) ^ n := by rw [pow_add]; norm_num
      have h1 : (-1 : ℂ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
      rw [h2, h1]
      ring

theorem cont_shift_one (a : ℕ → ℂ) (n : ℕ) :
    cont a (n + 2) = a 0 * cont (seqShift a 1) (n + 1) - cont (seqShift a 2) n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      have k1 : cont a 2 = a 1 * cont a 1 - cont a 0 := cont_succ_succ a 0
      have k2 : cont (seqShift a 1) 1 = (seqShift a 1) 0 := cont_one _
      rw [k1, k2]
      simp only [cont_one, cont_zero, seqShift_apply, Nat.zero_add]
      ring
  | one =>
      have k1 : cont a 3 = a 2 * cont a 2 - cont a 1 := cont_succ_succ a 1
      have k2 : cont a 2 = a 1 * cont a 1 - cont a 0 := cont_succ_succ a 0
      have k3 : cont (seqShift a 1) 2 = (seqShift a 1) 1 * cont (seqShift a 1) 1
          - cont (seqShift a 1) 0 := cont_succ_succ (seqShift a 1) 0
      have k4 : cont (seqShift a 2) 1 = (seqShift a 2) 0 := cont_one _
      rw [k1, k2, k3, k4]
      simp only [cont_one, cont_zero, seqShift_apply, Nat.zero_add, Nat.add_zero]
      ring
  | more n ih1 ih2 =>
      have k1 : cont a (n + 4) = a (n + 3) * cont a (n + 3) - cont a (n + 2) :=
        cont_succ_succ a (n + 2)
      have k2 : cont (seqShift a 1) (n + 3) =
          (seqShift a 1) (n + 2) * cont (seqShift a 1) (n + 2) - cont (seqShift a 1) (n + 1) :=
        cont_succ_succ (seqShift a 1) (n + 1)
      have k3 : cont (seqShift a 2) (n + 2) =
          (seqShift a 2) (n + 1) * cont (seqShift a 2) (n + 1) - cont (seqShift a 2) n :=
        cont_succ_succ (seqShift a 2) n
      rw [k1, k2, k3, ih1, ih2]
      simp only [seqShift_apply]
      ring

/-! ## The tridiagonal matrix -/

/-- The `n × n` tridiagonal matrix with diagonal `d` and off-diagonal entries `1`. -/
def triD (d : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if i = j then d i else 0)
    + (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0)

theorem triD_transpose (d : ℕ → ℂ) (n : ℕ) : Matrix.transpose (triD d n) = triD d n := by
  ext i j
  by_cases h : i = j
  · subst h; simp [triD]
  · simp only [Matrix.transpose_apply, triD, if_neg h, if_neg (Ne.symm h), or_comm]

theorem triD_self (d : ℕ → ℂ) (n : ℕ) (i : Fin n) : triD d n i i = d i := by
  simp only [triD, if_true, if_neg (by omega : ¬ ((i : ℕ) + 1 = i ∨ (i : ℕ) + 1 = i))]
  ring

theorem triD_succ (d : ℕ → ℂ) (n : ℕ) {i j : Fin n} (h : (i : ℕ) + 1 = j) :
    triD d n i j = 1 := by
  have hij : i ≠ j := by intro hh; rw [hh] at h; omega
  simp [triD, hij, h]

theorem triD_pred (d : ℕ → ℂ) (n : ℕ) {i j : Fin n} (h : (j : ℕ) + 1 = i) :
    triD d n i j = 1 := by
  have hij : i ≠ j := by intro hh; rw [hh] at h; omega
  simp [triD, hij, h]

theorem triD_zero (d : ℕ → ℂ) (n : ℕ) {i j : Fin n} (h : i ≠ j)
    (h' : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)) : triD d n i j = 0 := by
  simp [triD, h, h']

/-- `triD` with the first row and column removed is the tail. -/
theorem triD_tail (d : ℕ → ℂ) (n : ℕ) :
    (triD d (n + 1)).submatrix Fin.succ Fin.succ = triD (seqShift d 1) n := by
  ext i j
  simp only [Matrix.submatrix_apply, triD, Fin.val_succ, Fin.succ_inj, seqShift_apply]
  split_ifs <;> simp_all <;> omega

/-- `triD` with the last row and column removed is the leading block. -/
theorem triD_head (d : ℕ → ℂ) (n : ℕ) :
    (triD d (n + 1)).submatrix Fin.castSucc Fin.castSucc = triD d n := by
  ext i j
  simp only [Matrix.submatrix_apply, triD, Fin.val_castSucc, Fin.castSucc_inj]

/-! ## Determinants -/

/-- The determinant of a square matrix of size `m+1` whose first row is `e_0`. -/
theorem det_of_first_row {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h0 : M 0 0 = 1) (h : ∀ j : Fin (m + 1), j ≠ 0 → M 0 j = 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero,
    Finset.sum_eq_single (0 : Fin (m + 1)) (fun j _ hj => by rw [h j hj]; simp)
      (fun hc => absurd (Finset.mem_univ (0 : Fin (m + 1))) hc)]
  rw [h0, Fin.succAbove_zero]
  simp

/-- The determinant of a square matrix of size `m+1` whose last row is `e_last`. -/
theorem det_of_last_row {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h0 : M (Fin.last m) (Fin.last m) = 1)
    (h : ∀ j : Fin (m + 1), j ≠ Fin.last m → M (Fin.last m) j = 0) :
    M.det = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row M (Fin.last m),
    Finset.sum_eq_single (Fin.last m) (fun j _ hj => by rw [h j hj]; simp)
      (fun hc => absurd (Finset.mem_univ (Fin.last m)) hc)]
  have hsign : (-1 : ℂ) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ)) = 1 := by
    rw [Fin.val_last, show m + m = 2 * m by ring, pow_mul]
    norm_num
  rw [hsign, h0, Fin.succAbove_last]
  simp

/-- The determinant of a square matrix of size `m+1` whose first column is `e_0`. -/
theorem det_of_first_col {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h0 : M 0 0 = 1) (h : ∀ i : Fin (m + 1), i ≠ 0 → M i 0 = 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero,
    Finset.sum_eq_single (0 : Fin (m + 1)) (fun i _ hi => by rw [h i hi]; simp)
      (fun hc => absurd (Finset.mem_univ (0 : Fin (m + 1))) hc)]
  rw [h0, Fin.succAbove_zero]
  simp

/-- The determinant of a square matrix of size `m+1` whose last column is `e_last`. -/
theorem det_of_last_col {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h0 : M (Fin.last m) (Fin.last m) = 1)
    (h : ∀ i : Fin (m + 1), i ≠ Fin.last m → M i (Fin.last m) = 0) :
    M.det = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_column M (Fin.last m),
    Finset.sum_eq_single (Fin.last m) (fun i _ hi => by rw [h i hi]; simp)
      (fun hc => absurd (Finset.mem_univ (Fin.last m)) hc)]
  have hsign : (-1 : ℂ) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ)) = 1 := by
    rw [Fin.val_last, show m + m = 2 * m by ring, pow_mul]
    norm_num
  rw [hsign, h0, Fin.succAbove_last]
  simp

/-- **Determinant of the tridiagonal matrix.** -/
theorem det_triD (d : ℕ → ℂ) : ∀ n, (triD d n).det = cont d n
  | 0 => by simp
  | 1 => by simp [triD, triD_self]
  | n + 2 => by
      have hrow : ((Fin.succAbove (1 : Fin (n + 2)) : Fin (n + 1) → Fin (n + 2))
            ∘ (Fin.succ : Fin n → Fin (n + 1)))
          = (Fin.succ : Fin (n + 1) → Fin (n + 2)) ∘ (Fin.succ : Fin n → Fin (n + 1)) := by
        funext t
        apply Fin.ext
        simp only [Function.comp_apply, Fin.succAbove]
        split_ifs <;> simp_all <;> omega
      have hM1 : ((triD d (n + 2)).submatrix (Fin.succAbove 1) Fin.succ).det
          = cont (seqShift d 2) n := by
        have h0 : ((triD d (n + 2)).submatrix (Fin.succAbove 1) Fin.succ) 0 0 = 1 := by
          simp only [Matrix.submatrix_apply, triD, Fin.succAbove]
          split_ifs <;> simp_all <;> omega
        have hz : ∀ j : Fin (n + 1), j ≠ 0 →
            ((triD d (n + 2)).submatrix (Fin.succAbove 1) Fin.succ) 0 j = 0 := by
          intro j hj
          simp only [Matrix.submatrix_apply, triD, Fin.succAbove]
          split_ifs <;> simp_all <;> omega
        rw [det_of_first_row _ h0 hz]
        have hsub : ((triD d (n + 2)).submatrix (Fin.succAbove 1) Fin.succ).submatrix
            Fin.succ Fin.succ = triD (seqShift d 2) n := by
          rw [Matrix.submatrix_submatrix, hrow, ← Matrix.submatrix_submatrix, triD_tail,
            triD_tail, seqShift_seqShift]
        rw [hsub]
        exact det_triD (seqShift d 2) n
      have h1 : ((0 : Fin (n + 1)).succ : Fin (n + 2)) = 1 := by ext; simp
      have hM1' : ((triD d (n + 2)).submatrix (((0 : Fin (n + 1)).succ).succAbove)
            Fin.succ).det = cont (seqShift d 2) n := by
        rw [show ((0 : Fin (n + 1)).succ).succAbove
            = (Fin.succAbove (1 : Fin (n + 2))) by rw [h1]]
        exact hM1
      have hA10 : (triD d (n + 2)) ((0 : Fin (n + 1)).succ) 0 = 1 := by
        rw [h1]
        exact triD_pred d (n + 2) (by simp)
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
        Finset.sum_eq_single (0 : Fin (n + 1)) (fun i _ hi => by
          have hne : (i : ℕ) ≠ 0 := by
            intro h
            exact hi (Fin.ext (by rw [h]; simp))
          have hz : (triD d (n + 2)) (i.succ) 0 = 0 :=
            triD_zero d (n + 2) (Fin.succ_ne_zero i)
              (by simp only [Fin.val_succ, Fin.val_zero]; omega)
          rw [hz]
          ring)
          (fun hc => absurd (Finset.mem_univ (0 : Fin (n + 1))) hc)]
      have hsign0 : (-1 : ℂ) ^ ((0 : Fin (n + 2)) : ℕ) = 1 := by simp
      have hsign1 : (-1 : ℂ) ^ (((0 : Fin (n + 1)).succ : Fin (n + 2)) : ℕ) = -1 := by
        rw [h1]; simp
      rw [hsign0, hsign1, triD_self, Fin.succAbove_zero, triD_tail, hA10, hM1',
        cont_shift_one d n, det_triD (seqShift d 1) (n + 1)]
      simp only [Fin.val_zero]
      ring

/-- `pd (n+1)` is the continuant of the diagonal sequence. -/
theorem pd_eq_cont (α lam θ : ℝ) (E : ℂ) (n : ℕ) :
    pd α lam θ E (n + 1) = cont (fun i => E - ((amoPot α lam θ (i : ℤ) : ℝ) : ℂ)) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one =>
      have k : pd α lam θ E (1 + 1)
          = (E - ((amoPot α lam θ (((0 : ℕ) : ℤ)) : ℝ) : ℂ)) * pd α lam θ E 1
            - pd α lam θ E 0 := rfl
      rw [k, show pd α lam θ E 1 = (1 : ℂ) from rfl, show pd α lam θ E 0 = (0 : ℂ) from rfl]
      simp
  | more n ih1 ih2 =>
      have k : pd α lam θ E (n + 3)
          = (E - ((amoPot α lam θ (((n + 1 : ℕ) : ℤ)) : ℝ) : ℂ)) * pd α lam θ E (n + 2)
            - pd α lam θ E (n + 1) := rfl
      rw [show pd α lam θ E (n + 2 + 1) = pd α lam θ E (n + 3) from rfl, k, ih2, ih1,
        cont_succ_succ]

/-- `dirMat` is a tridiagonal matrix. -/
theorem dirMat_eq_triD (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    dirMat α lam θ E n = triD (fun i => ((amoPot α lam θ (i : ℤ) : ℝ) : ℂ) - E) n := by
  ext i j
  have c1 : (((i : ℕ) : ℤ) + 1 = ((j : ℕ) : ℤ)) ↔ ((i : ℕ) + 1 = (j : ℕ)) := by omega
  have c2 : (((j : ℕ) : ℤ) + 1 = ((i : ℕ) : ℤ)) ↔ ((j : ℕ) + 1 = (i : ℕ)) := by omega
  simp only [dirMat, triD, c1, c2]
  by_cases hA : ((i : ℕ) + 1 = (j : ℕ))
  · have hB : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
    simp [hA, hB]
  · by_cases hB : ((j : ℕ) + 1 = (i : ℕ))
    · simp [hA, hB]
    · simp [hA, hB]

end Work.TMC16Core.Basic

end
