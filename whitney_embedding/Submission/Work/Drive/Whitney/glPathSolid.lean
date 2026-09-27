import Mathlib

/-!
# Smooth paths in `GL_N(ℝ)` between operators of the same determinant sign

`GL_N(ℝ)` has two connected components, cut out by the sign of the determinant, and each of them is
path connected; here we prove the *smooth* form of that fact (for `N` arbitrary, including `N = 0`
and `N = 1`), together with the matrix-level elimination machinery (transvections, block
decomposition) that the proof uses.
-/

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace Work.Drive.Whitney

/-- The `C^∞` differentiability level, as an element of `WithTop ℕ∞`. -/
abbrev Smooth : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {n : ℕ}

/-! ## 1. The path predicate -/

/-- `Glue A B`: there is a smooth path of invertible (i.e. `det ≠ 0`) real matrices from `A` to `B`,
constant equal to `A` on `(-∞, 0]` and equal to `B` on `[1, ∞)`. -/
def Glue {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ h : ℝ → Matrix (Fin n) (Fin n) ℝ,
    (∀ t ≤ 0, h t = A) ∧ (∀ t ≥ 1, h t = B) ∧ ContDiff ℝ Smooth h ∧ ∀ t, (h t).det ≠ 0

theorem Glue.of_path {A B : Matrix (Fin n) (Fin n) ℝ} {h : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (h0 : h 0 = A) (h1 : h 1 = B) (hc : ContDiff ℝ Smooth h) (hd : ∀ t, (h t).det ≠ 0) :
    Glue A B := by
  refine ⟨fun t => h (Real.smoothTransition t), ?_, ?_, ?_, ?_⟩
  · intro t ht
    change h (Real.smoothTransition t) = A
    rw [Real.smoothTransition.zero_of_nonpos ht, h0]
  · intro t ht
    change h (Real.smoothTransition t) = B
    rw [Real.smoothTransition.one_of_one_le ht, h1]
  · exact hc.comp (Real.smoothTransition.contDiff (n := ⊤))
  · intro t; exact hd _

theorem contDiff_matrixMul {f g : ℝ → Matrix (Fin n) (Fin n) ℝ} (hf : ContDiff ℝ Smooth f)
    (hg : ContDiff ℝ Smooth g) : ContDiff ℝ Smooth (fun t => f t * g t) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun i : Fin n => fun j : Fin n => (f t * g t) i j)
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  simp only [Matrix.mul_apply]
  fun_prop

theorem Glue.symm {A B : Matrix (Fin n) (Fin n) ℝ} (h : Glue A B) : Glue B A := by
  obtain ⟨h, hA, hB, hc, hd⟩ := h
  refine ⟨fun t => h (1 - t), ?_, ?_, ?_, ?_⟩
  · intro t ht; exact hB _ (by linarith)
  · intro t ht; exact hA _ (by linarith)
  · exact hc.comp (by fun_prop)
  · intro t; exact hd _

theorem Glue.trans {A B C : Matrix (Fin n) (Fin n) ℝ} (h₁ : Glue A B) (h₂ : Glue B C) :
    Glue A C := by
  obtain ⟨f, fA, fB, hf, hfd⟩ := h₁
  obtain ⟨g, gB, gC, hg, hgd⟩ := h₂
  have hunit : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr (by have h := hfd 1; rwa [fB 1 le_rfl] at h)
  refine ⟨fun t => f (2*t) * B⁻¹ * g (2*t - 1), ?_, ?_, ?_, ?_⟩
  · intro t ht
    change f (2*t) * B⁻¹ * g (2*t - 1) = A
    rw [fA _ (by linarith), gB _ (by linarith), mul_assoc, Matrix.nonsing_inv_mul B hunit, mul_one]
  · intro t ht
    change f (2*t) * B⁻¹ * g (2*t - 1) = C
    rw [fB _ (by linarith), gC _ (by linarith), Matrix.mul_nonsing_inv B hunit, one_mul]
  · have h1 : ContDiff ℝ Smooth (fun t : ℝ => f (2*t)) := hf.comp (by fun_prop)
    have h2 : ContDiff ℝ Smooth (fun t : ℝ => g (2*t - 1)) := hg.comp (by fun_prop)
    exact contDiff_matrixMul (contDiff_matrixMul h1 contDiff_const) h2
  · intro t
    have h1 : (f (2*t)).det ≠ 0 := hfd _
    have h2 : (g (2*t-1)).det ≠ 0 := hgd _
    have h3 : (B⁻¹).det ≠ 0 := by
      intro hcon
      have h4 : (B⁻¹ * B).det = 1 := by rw [Matrix.nonsing_inv_mul B hunit, Matrix.det_one]
      rw [Matrix.det_mul, hcon, zero_mul] at h4
      exact zero_ne_one h4
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero h1 h3) h2

/-- `Glue` is compatible with (pointwise) multiplication. -/
theorem Glue.mul {A B C D : Matrix (Fin n) (Fin n) ℝ} (h₁ : Glue A B) (h₂ : Glue C D) :
    Glue (A * C) (B * D) := by
  obtain ⟨f, fA, fB, fc, fd⟩ := h₁
  obtain ⟨g, gA, gB, gc, gd⟩ := h₂
  refine ⟨fun t => f t * g t, ?_, ?_, ?_, ?_⟩
  · intro t ht
    change f t * g t = A * C
    rw [fA t ht, gA t ht]
  · intro t ht
    change f t * g t = B * D
    rw [fB t ht, gB t ht]
  · exact contDiff_matrixMul fc gc
  · intro t; rw [Matrix.det_mul]; exact mul_ne_zero (fd t) (gd t)

/-- `Glue` is invariant under left multiplication by a fixed invertible matrix. -/
theorem Glue.mulLeft {A L : Matrix (Fin n) (Fin n) ℝ} (hA : A.det ≠ 0) (h : Glue 1 L) :
    Glue A (L * A) := by
  obtain ⟨h, h0, h1, hc, hd⟩ := h
  refine Glue.of_path (h := fun t => h t * A) ?_ ?_ ?_ ?_
  · change h 0 * A = A; rw [h0 0 le_rfl, Matrix.one_mul]
  · change h 1 * A = L * A; rw [h1 1 le_rfl]
  · exact contDiff_matrixMul hc contDiff_const
  · intro t; rw [Matrix.det_mul]; exact mul_ne_zero (hd t) hA

/-- `Glue` is invariant under right multiplication by a fixed invertible matrix. -/
theorem Glue.mulRight {A L : Matrix (Fin n) (Fin n) ℝ} (hA : A.det ≠ 0) (h : Glue 1 L) :
    Glue A (A * L) := by
  obtain ⟨h, h0, h1, hc, hd⟩ := h
  refine Glue.of_path (h := fun t => A * h t) ?_ ?_ ?_ ?_
  · change A * h 0 = A; rw [h0 0 le_rfl, Matrix.mul_one]
  · change A * h 1 = A * L; rw [h1 1 le_rfl]
  · exact contDiff_matrixMul contDiff_const hc
  · intro t; rw [Matrix.det_mul]; exact mul_ne_zero hA (hd t)

/-! ## 2. Elementary matrices -/

theorem row_expansion (v : Fin n → ℝ) : v = ∑ k, v k • (1 : Matrix (Fin n) (Fin n) ℝ) k := by
  funext l
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem col_expansion (v : Fin n → ℝ) :
    v = ∑ k, v k • Matrix.col (1 : Matrix (Fin n) (Fin n) ℝ) k := by
  funext l
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
  · intro k _ hk; rw [if_neg (fun h : l = k => hk h.symm)]; simp
  · intro h; exact absurd (Finset.mem_univ l) h

theorem det_one_updateRow (j : Fin n) (v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateRow j v).det = v j := by
  conv_lhs => rw [row_expansion v]
  rw [Matrix.det_updateRow_sum]
  simp

theorem det_one_updateCol (j : Fin n) (v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateCol j v).det = v j := by
  have h : Matrix.transpose ((1 : Matrix (Fin n) (Fin n) ℝ).updateCol j v)
      = (1 : Matrix (Fin n) (Fin n) ℝ).updateRow j v := by
    rw [← Matrix.updateRow_transpose]
    congr 1
    ext i k
    simp only [Matrix.transpose_apply, Matrix.one_apply]
    by_cases hik : i = k <;> simp [hik, eq_comm]
  rw [← Matrix.det_transpose, h, det_one_updateRow]

theorem updateCol_mul (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (j : Fin (n+1)) (v : Fin (n+1) → ℝ)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k l : Fin (n+1)) :
    (A.updateCol j v * B) k l = (A * B) k l + (v k - A k j) * B j l := by
  have h : A.updateCol j v = A + (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateCol j
      (fun k => v k - A k j) := by
    ext k m
    by_cases hm : m = j
    · subst hm
      simp only [Matrix.add_apply, Matrix.updateCol_apply, if_true, Matrix.zero_apply]
      ring
    · simp only [Matrix.add_apply, Matrix.updateCol_apply, if_neg hm, Matrix.zero_apply, add_zero]
  rw [h, Matrix.add_mul, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp only [Matrix.updateCol_apply, if_true]
  · intro m _ hm; simp only [Matrix.updateCol_apply, if_neg hm, Matrix.zero_apply, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem mul_updateRow (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i : Fin (n+1)) (v : Fin (n+1) → ℝ) (k l : Fin (n+1)) :
    (A * B.updateRow i v) k l = (A * B) k l + A k i * (v l - B i l) := by
  have h : B.updateRow i v = B + (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateRow i
      (fun l => v l - B i l) := by
    ext m l
    by_cases hm : m = i
    · subst hm
      simp only [Matrix.add_apply, Matrix.updateRow_apply, if_true, Matrix.zero_apply]
      ring
    · simp only [Matrix.add_apply, Matrix.updateRow_apply, if_neg hm, Matrix.zero_apply, add_zero]
  rw [h, Matrix.mul_add, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp only [Matrix.updateRow_apply, if_true]
  · intro m _ hm; simp only [Matrix.updateRow_apply, if_neg hm, Matrix.zero_apply, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem contDiff_diagonal_fin1 {p : ℝ → ℝ} (hp : ContDiff ℝ Smooth p) :
    ContDiff ℝ Smooth (fun t : ℝ => Matrix.diagonal (fun _ : Fin 1 => p t)) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun i : Fin 1 => fun j : Fin 1 =>
    Matrix.diagonal (fun _ : Fin 1 => p t) i j)
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  fin_cases i; fin_cases j
  simp only [Matrix.diagonal_apply_eq]
  exact hp

theorem row_one_eq (i : Fin n) : (1 : Matrix (Fin n) (Fin n) ℝ) i = Pi.single i 1 := by
  funext l; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem vecMul_single_eq_row (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Matrix.vecMul (Pi.single i 1) A = A i := by
  rw [Matrix.single_vecMul, one_smul]
  ext j
  rw [Matrix.row_apply]

/-- The transvection `1 + c E_{ij}`. -/
def tran (c : ℝ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i
    ((1 : Matrix (Fin n) (Fin n) ℝ) i + c • (1 : Matrix (Fin n) (Fin n) ℝ) j)

theorem det_tran (c : ℝ) (i j : Fin n) (hij : i ≠ j) : (tran c i j).det = 1 := by
  rw [tran, det_one_updateRow]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, if_true]
  rw [if_neg (Ne.symm hij), mul_zero, add_zero]

theorem tran_mul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (i j : Fin n) :
    tran c i j * A = A.updateRow i (A i + c • A j) := by
  rw [tran, Matrix.updateRow_mul, Matrix.one_mul]
  congr 1
  rw [row_one_eq i, row_one_eq j, Matrix.add_vecMul, Matrix.smul_vecMul,
    vecMul_single_eq_row, vecMul_single_eq_row]

/-- The row operation matrix `row_i ↦ row_i + c_i · row_0` (for `i ≠ 0`). -/
def colZero (c : Fin (n+1) → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateCol 0 (fun i => if i = 0 then 1 else c i)

/-- The column operation matrix `col_j ↦ col_j + c_j · col_0` (for `j ≠ 0`). -/
def rowZero (c : Fin (n+1) → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateRow 0 (fun j => if j = 0 then 1 else c j)

theorem det_colZero (c : Fin (n+1) → ℝ) : (colZero c).det = 1 := by
  rw [colZero, det_one_updateCol]; simp

theorem det_rowZero (c : Fin (n+1) → ℝ) : (rowZero c).det = 1 := by
  rw [rowZero, det_one_updateRow]; simp

theorem colZero_mul (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (c : Fin (n+1) → ℝ) (i l : Fin (n+1)) :
    (colZero c * A) i l = A i l + (if i = 0 then 0 else c i) * A 0 l := by
  rw [colZero, updateCol_mul, Matrix.one_mul]
  congr 1
  congr 1
  by_cases hi : i = 0
  · subst hi
    have h1 : ((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) 0 0) = 1 := Matrix.one_apply_eq 0
    rw [if_pos rfl, h1, if_pos rfl, sub_self]
  · rw [if_neg hi, Matrix.one_apply_ne hi, sub_zero, if_neg hi]

theorem rowZero_mul (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (c : Fin (n+1) → ℝ) (i l : Fin (n+1)) :
    (A * rowZero c) i l = A i l + A i 0 * (if l = 0 then 0 else c l) := by
  rw [rowZero, mul_updateRow, Matrix.mul_one]
  congr 1
  congr 1
  by_cases hl : l = 0
  · subst hl
    have h1 : ((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) 0 0) = 1 := Matrix.one_apply_eq 0
    rw [if_pos rfl, h1, if_pos rfl, sub_self]
  · rw [if_neg hl, Matrix.one_apply_ne (Ne.symm hl), sub_zero, if_neg hl]

theorem colZero_zero : colZero (0 : Fin (n+1) → ℝ) = 1 := by
  have hv : (fun i : Fin (n+1) => (if i = 0 then (1:ℝ) else (0 : Fin (n+1) → ℝ) i))
      = fun i : Fin (n+1) => (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp only [if_neg hi, Matrix.one_apply_ne hi, Pi.zero_apply]
  rw [colZero, hv, Matrix.updateCol_eq_self]

theorem rowZero_zero : rowZero (0 : Fin (n+1) → ℝ) = 1 := by
  have hv : (fun i : Fin (n+1) => (if i = 0 then (1:ℝ) else (0 : Fin (n+1) → ℝ) i))
      = fun i : Fin (n+1) => (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) 0 i := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp only [if_neg hi, Matrix.one_apply_ne (Ne.symm hi), Pi.zero_apply]
  rw [rowZero, hv, Matrix.updateRow_eq_self]

theorem contDiff_tran_path (c : ℝ) (i j : Fin n) :
    ContDiff ℝ Smooth (fun t : ℝ => tran (t * c) i j) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun k : Fin n => fun l : Fin n => tran (t * c) i j k l)
  rw [contDiff_pi]; intro k
  rw [contDiff_pi]; intro l
  by_cases hk : k = i
  · subst hk
    simp only [tran, Matrix.updateRow_apply, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    split_ifs <;> fun_prop
  · simp only [tran, Matrix.updateRow_apply, if_neg hk, Matrix.one_apply]
    split_ifs <;> fun_prop

theorem contDiff_colZero_path (c : Fin (n+1) → ℝ) :
    ContDiff ℝ Smooth (fun t : ℝ => colZero (t • c)) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun i : Fin (n+1) => fun j : Fin (n+1) =>
    colZero (t • c) i j)
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  by_cases hj : j = 0
  · subst hj
    simp only [colZero, Matrix.updateCol_apply, if_true]
    split_ifs <;> fun_prop
  · simp only [colZero, Matrix.updateCol_apply, if_neg hj]
    fun_prop

theorem contDiff_rowZero_path (c : Fin (n+1) → ℝ) :
    ContDiff ℝ Smooth (fun t : ℝ => rowZero (t • c)) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun i : Fin (n+1) => fun j : Fin (n+1) =>
    rowZero (t • c) i j)
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  by_cases hi : i = 0
  · subst hi
    simp only [rowZero, Matrix.updateRow_apply, if_true]
    split_ifs <;> fun_prop
  · simp only [rowZero, Matrix.updateRow_apply, if_neg hi]
    fun_prop

theorem glue_tran (c : ℝ) (i j : Fin n) (hij : i ≠ j) : Glue 1 (tran c i j) := by
  refine Glue.of_path (h := fun t : ℝ => tran (t * c) i j) ?_ ?_ ?_ ?_
  · rw [zero_mul, tran]
    simp
  · rw [one_mul]
  · exact contDiff_tran_path c i j
  · intro t; rw [det_tran _ _ _ hij]; norm_num

theorem glue_colZero (c : Fin (n+1) → ℝ) : Glue 1 (colZero c) := by
  refine Glue.of_path (h := fun t : ℝ => colZero (t • c)) ?_ ?_ ?_ ?_
  · rw [zero_smul, colZero_zero]
  · rw [one_smul]
  · exact contDiff_colZero_path c
  · intro t; rw [det_colZero]; norm_num

theorem glue_rowZero (c : Fin (n+1) → ℝ) : Glue 1 (rowZero c) := by
  refine Glue.of_path (h := fun t : ℝ => rowZero (t • c)) ?_ ?_ ?_ ?_
  · rw [zero_smul, rowZero_zero]
  · rw [one_smul]
  · exact contDiff_rowZero_path c
  · intro t; rw [det_rowZero]; norm_num

/-! ## 3. Block matrices and the canonical forms -/

/-- The matrix `diag(a, A)`. -/
def blockDiag {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

/-- The trailing block of a matrix on `Fin (n+1)`. -/
def tail {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.succ Fin.succ

theorem blockDiag_zero_zero {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    blockDiag a A 0 0 = a := by simp [blockDiag]

theorem blockDiag_zero_succ {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    blockDiag a A 0 j.succ = 0 := by simp [blockDiag]

theorem blockDiag_succ_zero {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    blockDiag a A i.succ 0 = 0 := by simp [blockDiag]

theorem blockDiag_succ_succ {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    blockDiag a A i.succ j.succ = A i j := by simp [blockDiag]

theorem tail_blockDiag {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    tail (blockDiag a A) = A := by
  ext i j
  simp [tail, blockDiag, Matrix.submatrix]

theorem det_blockDiag {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (blockDiag a A).det = a * A.det := by
  have h := Matrix.det_succ_row_zero (blockDiag a A)
  rw [Finset.sum_eq_single (0 : Fin (n+1))] at h
  · rw [h, Fin.succAbove_zero]
    have h2 : (blockDiag a A).submatrix Fin.succ Fin.succ = A := tail_blockDiag a A
    rw [h2]
    simp [blockDiag]
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp [blockDiag]
  · intro h; exact absurd (Finset.mem_univ 0) h

theorem eq_blockDiag_of {n : ℕ} {a : ℝ} {B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (h00 : B 0 0 = a) (h0j : ∀ j, j ≠ 0 → B 0 j = 0) (hi0 : ∀ i, i ≠ 0 → B i 0 = 0) :
    B = blockDiag a (tail B) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · subst h
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; rw [h00]; simp [blockDiag]
    · rw [h0j _ (Fin.succ_ne_zero j')]; simp [blockDiag]
  · rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; rw [hi0 _ (Fin.succ_ne_zero i')]; simp [blockDiag]
    · simp [blockDiag, tail, Matrix.submatrix]

/-- The canonical matrices: the identity for `true`, and `diag(1, …, 1, -1)` for `false`. -/
def canon : (n : ℕ) → Bool → Matrix (Fin n) (Fin n) ℝ
  | 0, _ => 1
  | 1, true => 1
  | 1, false => Matrix.diagonal (fun _ : Fin 1 => (-1 : ℝ))
  | (n+2), true => 1
  | (n+2), false => blockDiag 1 (canon (n+1) false)

theorem canon_true (n : ℕ) : canon n true = 1 := by
  rcases n with _ | _ | m <;> rfl

theorem canon_one_false : canon 1 false = Matrix.diagonal (fun _ : Fin 1 => (-1 : ℝ)) := rfl

theorem blockDiag_one_one {n : ℕ} : blockDiag 1 (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  simp only [blockDiag, Matrix.one_apply]
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · subst h
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; simp
    · simp [Ne.symm (Fin.succ_ne_zero j')]
  · rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; simp [Ne.symm (Fin.succ_ne_zero i')]
    · simp

theorem blockDiag_one_canon (m : ℕ) (b : Bool) :
    blockDiag 1 (canon (m+1) b) = canon (m+2) b := by
  cases b
  · rfl
  · rw [canon_true (m+1), canon_true (m+2), blockDiag_one_one]

theorem contDiff_blockDiag_path {n : ℕ} {p : ℝ → ℝ} {γ : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hp : ContDiff ℝ Smooth p) (hγ : ContDiff ℝ Smooth γ) :
    ContDiff ℝ Smooth (fun t => blockDiag (p t) (γ t)) := by
  change ContDiff ℝ Smooth (fun t : ℝ => fun i : Fin (n+1) => fun j : Fin (n+1) =>
    blockDiag (p t) (γ t) i j)
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · subst h
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; simpa [blockDiag] using hp
    · simpa [blockDiag] using (contDiff_const : ContDiff ℝ Smooth (fun _ : ℝ => (0:ℝ)))
  · rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
    · subst h; simpa [blockDiag] using (contDiff_const : ContDiff ℝ Smooth (fun _ : ℝ => (0:ℝ)))
    · simpa [blockDiag] using (contDiff_pi.mp (contDiff_pi.mp hγ i') j')

theorem firstCol_mul {m : ℕ} (M A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ)
    (hcol : ∀ i, i ≠ 0 → A i 0 = 0) (i : Fin (m+2)) :
    (M * A) i 0 = M i 0 * A 0 0 := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single 0 (fun k _ hk => by rw [hcol k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ 0) h)]

theorem step4_pos {m : ℕ} (A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ)
    (hcol : ∀ i, i ≠ 0 → A i 0 = 0) (h0 : A 0 0 < 0) :
    0 < (((tran (n := m+2) (-2) 0 1) * (tran (n := m+2) 1 1 0)) * A) 0 0 := by
  have h01 : (0 : Fin (m+2)) ≠ 1 := by norm_num
  have h10 : (1 : Fin (m+2)) ≠ 0 := by norm_num
  have hA : (tran (n := m+2) 1 1 0) 0 0 = 1 := by
    rw [tran, Matrix.updateRow_apply, if_neg h01]
    exact Matrix.one_apply_eq 0
  have hB : (tran (n := m+2) 1 1 0) 1 0 = 1 := by
    rw [tran, Matrix.updateRow_apply, if_pos rfl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ((1 : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 1 0) = 0 := Matrix.one_apply_ne h10
    have e2 : ((1 : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0) = 1 := Matrix.one_apply_eq 0
    rw [e1, e2, mul_one, zero_add]
  have hentry : ((tran (n := m+2) (-2) 0 1) * (tran (n := m+2) 1 1 0)) 0 0 = -1 := by
    rw [tran_mul, Matrix.updateRow_apply, if_pos rfl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hA, hB]
    norm_num
  rw [firstCol_mul ((tran (n := m+2) (-2) 0 1) * (tran (n := m+2) 1 1 0)) A hcol 0, hentry]
  linarith

/-! ## 4. The elimination steps -/

/-- Killing the first column, once the pivot `(P * A) 0 0` is positive. -/
theorem stepA_kill {m : ℕ} (A P : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (hdet : P.det = 1)
    (hpath : Glue 1 P) (hpos : 0 < (P * A) 0 0) :
    ∃ L : Matrix (Fin (m+2)) (Fin (m+2)) ℝ, L.det = 1 ∧ Glue 1 L ∧
      0 < (L * A) 0 0 ∧ ∀ i : Fin (m+2), i ≠ 0 → (L * A) i 0 = 0 := by
  have hne : (P * A) 0 0 ≠ 0 := ne_of_gt hpos
  refine ⟨colZero (fun i => if i = 0 then 0 else -((P * A) i 0)/((P * A) 0 0)) * P,
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_colZero, hdet, mul_one]
  · have hg := Glue.mul
      (glue_colZero (fun i => if i = 0 then 0 else -((P * A) i 0)/((P * A) 0 0))) hpath
    simpa using hg
  · rw [Matrix.mul_assoc, colZero_mul]
    simpa using hpos
  · intro i hi
    rw [Matrix.mul_assoc, colZero_mul]
    simp only [if_neg hi]
    have h1 : (-((P * A) i 0)/((P * A) 0 0)) * ((P * A) 0 0) = -((P * A) i 0) := by
      field_simp
    rw [h1]
    ring

/-- Making the first column equal to `c · e₀` with `c > 0`. -/
theorem stepA {m : ℕ} (A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (hA : A.det ≠ 0) :
    ∃ L : Matrix (Fin (m+2)) (Fin (m+2)) ℝ, L.det = 1 ∧ Glue 1 L ∧
      0 < (L * A) 0 0 ∧ ∀ i : Fin (m+2), i ≠ 0 → (L * A) i 0 = 0 := by
  classical
  have hvne : (fun i : Fin (m+2) => A i 0) ≠ 0 := by
    intro h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 (fun i => congrFun h i))
  have h01 : (0 : Fin (m+2)) ≠ 1 := by norm_num
  have h10 : (1 : Fin (m+2)) ≠ 0 := by norm_num
  rcases lt_trichotomy (A 0 0) 0 with hneg | hzero | hpos
  · -- `A 0 0 < 0`
    by_cases hex : ∃ k : Fin (m+2), k ≠ 0 ∧ A k 0 ≠ 0
    · obtain ⟨k, hk0, hkv⟩ := hex
      exact stepA_kill A (tran ((1 - A 0 0)/(A k 0)) 0 k) (det_tran _ 0 k (Ne.symm hk0))
        (glue_tran _ 0 k (Ne.symm hk0)) (by
          rw [tran_mul, Matrix.updateRow_apply, if_pos rfl]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [div_mul_cancel₀ (1 - A 0 0) hkv]
          linarith)
    · push_neg at hex
      refine stepA_kill A (tran (-2) 0 1 * tran 1 1 0) ?_ ?_ ?_
      · rw [Matrix.det_mul, det_tran _ _ _ h01, det_tran _ _ _ h10, mul_one]
      · have hg := Glue.mul (glue_tran (-2) 0 1 h01) (glue_tran 1 1 0 h10)
        simpa using hg
      · exact step4_pos A hex hneg
  · -- `A 0 0 = 0`
    have hex : ∃ k : Fin (m+2), k ≠ 0 ∧ A k 0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hvne (funext fun i => by
        rcases eq_or_ne i 0 with h' | h'
        · subst h'; exact hzero
        · exact h i h')
    obtain ⟨k, hk0, hkv⟩ := hex
    exact stepA_kill A (tran (1/(A k 0)) 0 k) (det_tran _ 0 k (Ne.symm hk0))
      (glue_tran _ 0 k (Ne.symm hk0)) (by
        rw [tran_mul, Matrix.updateRow_apply, if_pos rfl]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hzero, zero_add, div_mul_cancel₀ (1:ℝ) hkv]
        norm_num)
  · -- `0 < A 0 0`
    exact stepA_kill A 1 Matrix.det_one
      (Glue.of_path (h := fun _ : ℝ => 1) rfl rfl contDiff_const (fun _ => by simp))
      (by rw [Matrix.one_mul]; exact hpos)

/-- Killing the first row, once the first column is `c · e₀` with `c > 0`. -/
theorem stepB {m : ℕ} (B : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (h00 : 0 < B 0 0)
    (hcol : ∀ i, i ≠ 0 → B i 0 = 0) :
    ∃ M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ, M.det = 1 ∧ Glue 1 M ∧ (B * M) 0 0 = B 0 0 ∧
      (∀ j, j ≠ 0 → (B * M) 0 j = 0) ∧ (∀ i, i ≠ 0 → (B * M) i 0 = 0) := by
  have hne : B 0 0 ≠ 0 := ne_of_gt h00
  refine ⟨rowZero (fun j => if j = 0 then 0 else -(B 0 j)/B 0 0), det_rowZero _, ?_, ?_, ?_, ?_⟩
  · exact glue_rowZero _
  · rw [rowZero_mul, if_pos rfl, mul_zero, add_zero]
  · intro j hj
    rw [rowZero_mul]
    simp only [if_neg hj]
    field_simp
    ring
  · intro i hi
    rw [rowZero_mul, if_pos rfl, mul_zero, add_zero]
    exact hcol i hi

/-! ## 5. The induction -/

theorem glue_canon_succ (m : ℕ) (A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (hA : A.det ≠ 0)
    (ih : ∀ B : Matrix (Fin (m+1)) (Fin (m+1)) ℝ, B.det ≠ 0 →
      Glue B (canon (m+1) (decide (0 < B.det)))) :
    Glue A (canon (m+2) (decide (0 < A.det))) := by
  obtain ⟨L, hLdet, hLpath, hLpos, hLcol⟩ := stepA A hA
  have hLAdet : (L * A).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero (by rw [hLdet]; norm_num) hA
  have hglue1 : Glue A (L * A) := Glue.mulLeft hA hLpath
  obtain ⟨M, hMdet, hMpath, hM00, hM0j, hMi0⟩ := stepB (L * A) hLpos hLcol
  set B : Matrix (Fin (m+2)) (Fin (m+2)) ℝ := L * A * M with hB
  have hB00 : B 0 0 = (L * A) 0 0 := hM00
  have hB0j : ∀ j, j ≠ 0 → B 0 j = 0 := hM0j
  have hBi0 : ∀ i, i ≠ 0 → B i 0 = 0 := hMi0
  have hgBdet : B.det = A.det := by
    rw [hB, Matrix.det_mul, Matrix.det_mul, hMdet, mul_one, hLdet, one_mul]
  have hglue2 : Glue (L * A) B := Glue.mulRight hLAdet hMpath
  have hBeq : B = blockDiag (B 0 0) (tail B) := eq_blockDiag_of rfl hB0j hBi0
  have hBpos : 0 < B 0 0 := by rw [hB00]; exact hLpos
  have hBdetfactor : B.det = B 0 0 * (tail B).det := by
    conv_lhs => rw [hBeq]
    rw [det_blockDiag]
  have hdetrel : B 0 0 * (tail B).det = A.det := by rw [← hBdetfactor, hgBdet]
  have htb : (tail B).det ≠ 0 := by
    intro h; rw [h, mul_zero] at hdetrel; exact hA hdetrel.symm
  have hiff : (0 < (tail B).det) ↔ (0 < A.det) := by
    constructor
    · intro h
      rcases lt_trichotomy (tail B).det 0 with hlt | heq | hgt
      · exfalso
        have hc : A.det < 0 := by
          rw [← hdetrel]; exact mul_neg_of_pos_of_neg hBpos hlt
        linarith
      · exact absurd heq htb
      · rw [← hdetrel]; exact mul_pos hBpos hgt
    · intro h
      rcases lt_trichotomy (tail B).det 0 with hlt | heq | hgt
      · exfalso
        have hc : A.det < 0 := by
          rw [← hdetrel]; exact mul_neg_of_pos_of_neg hBpos hlt
        linarith
      · exact absurd heq htb
      · exact hgt
  have hsign : (decide (0 < (tail B).det)) = (decide (0 < A.det)) := by
    by_cases h : 0 < (tail B).det
    · rw [decide_eq_true h, decide_eq_true (hiff.mp h)]
    · rw [decide_eq_false h, decide_eq_false (fun hc => h (hiff.mpr hc))]
  obtain ⟨γ, γ0, γ1, γc, γd⟩ := ih (tail B) htb
  have hglue3 : Glue B (canon (m+2) (decide (0 < A.det))) := by
    refine Glue.of_path
      (h := fun t => blockDiag ((1 - Real.smoothTransition t) * (B 0 0) +
        Real.smoothTransition t * 1) (γ t)) ?_ ?_ ?_ ?_
    · change blockDiag ((1 - Real.smoothTransition 0) * (B 0 0) + Real.smoothTransition 0 * 1)
        (γ 0) = B
      rw [Real.smoothTransition.zero, sub_zero, one_mul, zero_mul, add_zero, γ0 0 le_rfl]
      exact hBeq.symm
    · change blockDiag ((1 - Real.smoothTransition 1) * (B 0 0) + Real.smoothTransition 1 * 1)
        (γ 1) = canon (m+2) (decide (0 < A.det))
      rw [Real.smoothTransition.one, sub_self, zero_mul, zero_add, one_mul, γ1 1 le_rfl, hsign,
        blockDiag_one_canon]
    · refine contDiff_blockDiag_path ?_ γc
      fun_prop
    · intro t
      rw [det_blockDiag]
      refine mul_ne_zero ?_ (γd t)
      have hφ0 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
      have hφ1 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
      rcases lt_or_eq_of_le hφ1 with hlt | heq
      · nlinarith
      · rw [heq]; norm_num
  exact Glue.trans (Glue.trans hglue1 hglue2) hglue3

theorem glue_canon (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    Glue A (canon n (decide (0 < A.det))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · -- `n = 0`
      refine Glue.of_path (h := fun _ : ℝ => A) rfl ?_ contDiff_const ?_
      · ext i j; exact Fin.elim0 i
      · intro t
        rw [show A.det = 1 from Matrix.det_isEmpty]
        norm_num
    · -- `n = 1`
      set a : ℝ := A 0 0 with ha
      have hAeq : A = Matrix.diagonal (fun _ : Fin 1 => a) := by
        ext i j; fin_cases i; fin_cases j
        simp [Matrix.diagonal_apply, ha]
      have hdet : A.det = a := by rw [hAeq, Matrix.det_diagonal]; simp
      have hne : a ≠ 0 := by rw [← hdet]; exact hA
      rcases lt_trichotomy a 0 with hneg | hzero | hpos
      · -- negative
        have hdec : (decide (0 < A.det)) = false := by
          rw [hdet]; exact decide_eq_false (not_lt.mpr (le_of_lt hneg))
        refine Glue.of_path (h := fun t : ℝ => Matrix.diagonal
          (fun _ : Fin 1 => (1 - Real.smoothTransition t) * a +
            Real.smoothTransition t * (-1))) ?_ ?_ ?_ ?_
        · have hfun : (fun _ : Fin 1 => (1 - Real.smoothTransition 0) * a +
              Real.smoothTransition 0 * (-1)) = fun _ : Fin 1 => a := by
            funext i
            rw [Real.smoothTransition.zero]
            ring
          show Matrix.diagonal (fun _ : Fin 1 => (1 - Real.smoothTransition 0) * a +
              Real.smoothTransition 0 * (-1)) = A
          rw [hfun]
          exact hAeq.symm
        · have hfun : (fun _ : Fin 1 => (1 - Real.smoothTransition 1) * a +
              Real.smoothTransition 1 * (-1)) = fun _ : Fin 1 => (-1 : ℝ) := by
            funext i
            rw [Real.smoothTransition.one]
            ring
          show Matrix.diagonal (fun _ : Fin 1 => (1 - Real.smoothTransition 1) * a +
              Real.smoothTransition 1 * (-1)) = canon 1 (decide (0 < A.det))
          rw [hfun, hdec]
          exact canon_one_false.symm
        · exact contDiff_diagonal_fin1 (p := fun t : ℝ =>
            (1 - Real.smoothTransition t) * a + Real.smoothTransition t * (-1)) (by fun_prop)
        · intro t
          rw [Matrix.det_diagonal]
          simp
          have hφ0 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
          have hφ1 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
          by_cases ht : Real.smoothTransition t = 0
          · rw [ht]
            simp only [sub_zero, one_mul, zero_mul, neg_zero, add_zero]
            exact ne_of_lt hneg
          · have ht0 : 0 < Real.smoothTransition t := lt_of_le_of_ne hφ0 (Ne.symm ht)
            nlinarith
      · exact absurd (by rw [hzero] at hne; exact hne rfl) (by simp)
      · -- positive
        have hdec : (decide (0 < A.det)) = true := by
          rw [hdet]; exact decide_eq_true hpos
        refine Glue.of_path (h := fun t : ℝ => Matrix.diagonal
          (fun _ : Fin 1 => (1 - Real.smoothTransition t) * a +
            Real.smoothTransition t * 1)) ?_ ?_ ?_ ?_
        · have hfun : (fun _ : Fin 1 => (1 - Real.smoothTransition 0) * a +
              Real.smoothTransition 0 * 1) = fun _ : Fin 1 => a := by
            funext i
            rw [Real.smoothTransition.zero]
            ring
          show Matrix.diagonal (fun _ : Fin 1 => (1 - Real.smoothTransition 0) * a +
              Real.smoothTransition 0 * 1) = A
          rw [hfun]
          exact hAeq.symm
        · have hfun : (fun _ : Fin 1 => (1 - Real.smoothTransition 1) * a +
              Real.smoothTransition 1 * 1) = fun _ : Fin 1 => (1 : ℝ) := by
            funext i
            rw [Real.smoothTransition.one]
            ring
          show Matrix.diagonal (fun _ : Fin 1 => (1 - Real.smoothTransition 1) * a +
              Real.smoothTransition 1 * 1) = canon 1 (decide (0 < A.det))
          rw [hfun, hdec, canon_true]
          ext i j; fin_cases i; fin_cases j; simp [Matrix.diagonal_apply, Matrix.one_apply]
        · exact contDiff_diagonal_fin1 (p := fun t : ℝ =>
            (1 - Real.smoothTransition t) * a + Real.smoothTransition t * 1) (by fun_prop)
        · intro t
          rw [Matrix.det_diagonal]
          simp
          have hφ0 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
          have hφ1 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
          by_cases ht : Real.smoothTransition t = 1
          · rw [ht]; norm_num
          · have ht1 : Real.smoothTransition t < 1 := lt_of_le_of_ne hφ1 ht
            nlinarith
    · exact glue_canon_succ m A hA (fun B hB => ih (m+1) (by omega) B hB)

/-! ## 6. From matrices to continuous linear equivalences -/

theorem contDiff_toEuclideanCLM_comp {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hM : ContDiff ℝ Smooth M) :
    ContDiff ℝ Smooth (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M t)) := by
  rw [contDiff_clm_apply_iff]
  intro y
  rw [contDiff_piLp (p := 2)]
  intro i
  have h2 : ContDiff ℝ Smooth (fun t : ℝ => Matrix.mulVec (M t) (fun j => y j) i) := by
    rw [show (fun t : ℝ => Matrix.mulVec (M t) (fun j => y j) i)
        = (fun t : ℝ => ∑ j, M t i j * y j) from by
      funext t; simp [Matrix.mulVec, dotProduct]]
    fun_prop
  convert h2 using 1
  ext t
  have h : WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M t) y)
      = Matrix.mulVec (M t) (WithLp.ofLp y) :=
    Matrix.ofLp_toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M t) y
  have h2' := congrFun h i
  simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using h2'

/-- Assembling the final path from a matrix path and the operators it corresponds to. -/
theorem final_assembly {N : ℕ} (MA MB : Matrix (Fin N) (Fin N) ℝ) (h : Glue MA MB)
    (A B : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
    (hA : Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) MA =
      (A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (hB : Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) MB =
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) :
    ∃ H : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)),
      H 0 = A ∧ H 1 = B ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun r : ℝ => (H r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) := by
  obtain ⟨h, h0, h1, hc, hd⟩ := h
  let H : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) := fun t =>
    ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin N)) (Units.map
      (RingEquiv.toMonoidHom (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toRingEquiv)
      ((Matrix.isUnit_iff_isUnit_det (h t)).mpr (isUnit_iff_ne_zero.mpr (hd t))).unit)
  have hHcoe : ∀ t, ((H t : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
      = Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (h t) := by
    intro t
    apply ContinuousLinearMap.ext
    intro x
    show ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin N)) (Units.map
      (RingEquiv.toMonoidHom (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toRingEquiv)
      ((Matrix.isUnit_iff_isUnit_det (h t)).mpr (isUnit_iff_ne_zero.mpr (hd t))).unit) x = _
    rw [ContinuousLinearEquiv.unitsEquiv_apply]
    simp
  refine ⟨H, ?_, ?_, ?_⟩
  · apply ContinuousLinearEquiv.coe_injective
    rw [hHcoe 0, h0 0 le_rfl, hA]
  · apply ContinuousLinearEquiv.coe_injective
    rw [hHcoe 1, h1 1 le_rfl, hB]
  · have : (fun r : ℝ => (H r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
        = fun r => Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (h r) := funext hHcoe
    rw [this]
    exact contDiff_toEuclideanCLM_comp hc

theorem glPathSolid {N : ℕ} (A B : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
    (hAB : 0 < (LinearMap.det (A : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) *
      (LinearMap.det (B : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)))) :
    ∃ h : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)),
      h 0 = A ∧ h 1 = B ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun r : ℝ => (h r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) := by
  classical
  set MA : Matrix (Fin N) (Fin N) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm
      (A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) with hMA
  set MB : Matrix (Fin N) (Fin N) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) with hMB
  have hMAc : Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) MA =
      (A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
    rw [hMA]; simp
  have hMBc : Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) MB =
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
    rw [hMB]; simp
  have hdetA : LinearMap.det (A : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = MA.det := by
    change LinearMap.det ((A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = MA.det
    rw [← hMAc]
    change LinearMap.det (Matrix.toEuclideanLin (m := Fin N) (n := Fin N) MA) = MA.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hdetB : LinearMap.det (B : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = MB.det := by
    change LinearMap.det ((B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = MB.det
    rw [← hMBc]
    change LinearMap.det (Matrix.toEuclideanLin (m := Fin N) (n := Fin N) MB) = MB.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hprod : 0 < MA.det * MB.det := by rw [← hdetA, ← hdetB]; exact hAB
  rcases mul_pos_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hneA : MA.det ≠ 0 := ne_of_gt ha
    have hneB : MB.det ≠ 0 := ne_of_gt hb
    have hsign : (decide (0 < MA.det)) = (decide (0 < MB.det)) := by
      rw [decide_eq_true ha, decide_eq_true hb]
    exact final_assembly MA MB
      (Glue.trans (glue_canon N MA hneA) (Glue.symm (by rw [hsign]; exact glue_canon N MB hneB)))
      A B hMAc hMBc
  · have hneA : MA.det ≠ 0 := ne_of_lt ha
    have hneB : MB.det ≠ 0 := ne_of_lt hb
    have hsign : (decide (0 < MA.det)) = (decide (0 < MB.det)) := by
      rw [decide_eq_false (not_lt.mpr (le_of_lt ha)), decide_eq_false (not_lt.mpr (le_of_lt hb))]
    exact final_assembly MA MB
      (Glue.trans (glue_canon N MA hneA) (Glue.symm (by rw [hsign]; exact glue_canon N MB hneB)))
      A B hMAc hMBc

end Work.Drive.Whitney
