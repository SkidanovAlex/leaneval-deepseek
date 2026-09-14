import Mathlib
import Submission.Commons.Data.Matrix.reduce_col_to_single_nonzero

open scoped BigOperators
open Matrix

namespace Commons.Data.Matrix

set_option autoImplicit false

/-- Split `Fin (n+1)` into its first element `0` (labelled by `Unit`)
and the rest `1..n` (labelled by `Fin n` via `Fin.succ`). -/
private def eTop (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ : Unit => (0 : Fin (n + 1))) (fun i : Fin n => i.succ)
  invFun i := Fin.cases (Sum.inl Unit.unit) (fun j : Fin n => Sum.inr j) i
  left_inv x := by
    cases x with
    | inl a => cases a <;> simp [Fin.cases_zero]
    | inr b => simp [Fin.cases_succ]
  right_inv i := by
    refine Fin.cases ?h0 ?hs i
    · simp [Fin.cases_zero]
    · intro j
      simp [Fin.cases_succ]

@[simp] private lemma eTop_inl (n : ℕ) : eTop n (Sum.inl Unit.unit) = (0 : Fin (n + 1)) := by
  simp [eTop]
@[simp] private lemma eTop_inr (n : ℕ) (i : Fin n) : eTop n (Sum.inr i) = (i : Fin n).succ := by
  simp [eTop]
@[simp] private lemma eTop_symm_zero (n : ℕ) : (eTop n).symm (0 : Fin (n + 1)) = Sum.inl Unit.unit := by
  rw [Equiv.symm_apply_eq, eTop_inl]
@[simp] private lemma eTop_symm_succ (n : ℕ) (i : Fin n) : (eTop n).symm (i : Fin n).succ = Sum.inr i := by
  rw [Equiv.symm_apply_eq, eTop_inr]

/-- `(U * A) i j` equals `U.mulVec` applied to column `j` of `A`, at row `i`. -/
private lemma mulVec_col {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (A : Matrix (Fin d) (Fin d) ℤ)
    (c : Fin d) (r : Fin d) :
    (U.mulVec (fun k : Fin d => A k c)) r = (U * A) r c := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma not_lt_fin_zero {k : ℕ} (j : Fin (k + 1)) : ¬ j < (0 : Fin (k + 1)) := by
  intro h
  have hv : (j : Fin (k + 1)).val < (0 : Fin (k + 1)).val := (Fin.lt_def.mp h)
  have hz : (0 : Fin (k + 1)).val = 0 := by simp
  omega

/-- Row-reduction Hermite existence: any invertible integer square matrix can be brought to
upper-triangular form by left multiplication with a unimodular integer matrix. -/
private theorem upperTri {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnit U.det ∧ ∀ (i j : Fin d), j < i → (U.mulVec (fun r : Fin d => A r j)) i = 0 := by
  induction d with
  | zero =>
      refine ⟨1, ?_, ?_⟩
      · simpa using (isUnit_one : IsUnit (1 : ℤ))
      · intro i j hij
        exact False.elim (Fin.elim0 i)
  | succ n ih =>
      classical
      let A0 : Fin (n + 1) → ℤ := fun i => A i 0
      have hA0 : ∃ i : Fin (n + 1), A0 i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
      haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      obtain ⟨W, g, hWunit, hg, hW0, hWrest⟩ := reduce_col_to_single_nonzero A0 hA0
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := W * A
      have hB0 : ∀ i : Fin (n + 1), i ≠ 0 → B i 0 = 0 := by
        intro i hi
        change (W * A) i 0 = 0
        rw [← mulVec_col W A 0 i]
        simpa [A0] using hWrest i hi
      have hB00 : B 0 0 = g := by
        change (W * A) 0 0 = g
        rw [← mulVec_col W A 0 (0 : Fin (n + 1))]
        simpa [A0] using hW0
      have hBdet : B.det ≠ 0 := by
        dsimp [B]
        rw [Matrix.det_mul]
        exact mul_ne_zero (IsUnit.ne_zero hWunit) hA
      let M : Matrix (Fin n) (Fin n) ℤ := fun i j => B i.succ j.succ
      let e : Unit ⊕ Fin n ≃ Fin (n + 1) := eTop n
      let Bs : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℤ := reindex e.symm e.symm B
      let G : Matrix Unit Unit ℤ := Matrix.of (fun _ _ => g)
      let R : Matrix Unit (Fin n) ℤ := Matrix.of (fun _ j => B 0 j.succ)
      have hBs : Bs = Matrix.fromBlocks G R 0 M := by
        ext r c
        cases r
        · rename_i u
          cases u
          cases c
          · rename_i v
            cases v
            change Bs (Sum.inl Unit.unit) (Sum.inl Unit.unit) = g
            have h1 : Bs (Sum.inl Unit.unit) (Sum.inl Unit.unit) = B 0 0 := by
              simp [Bs, e, Matrix.reindex, Matrix.submatrix]
            rw [h1]
            exact hB00
          · rename_i j
            change Bs (Sum.inl Unit.unit) (Sum.inr j) = B 0 j.succ
            have h1 : Bs (Sum.inl Unit.unit) (Sum.inr j) = B 0 j.succ := by
              simp [Bs, e, Matrix.reindex, Matrix.submatrix]
            exact h1
        · rename_i i
          cases c
          · rename_i v
            cases v
            change Bs (Sum.inr i) (Sum.inl Unit.unit) = 0
            have h1 : Bs (Sum.inr i) (Sum.inl Unit.unit) = B i.succ 0 := by
              simp [Bs, e, Matrix.reindex, Matrix.submatrix]
            rw [h1]
            exact hB0 i.succ (Fin.succ_ne_zero i)
          · rename_i j
            change Bs (Sum.inr i) (Sum.inr j) = M i j
            have h1 : Bs (Sum.inr i) (Sum.inr j) = B i.succ j.succ := by
              simp [Bs, e, Matrix.reindex, Matrix.submatrix]
            rw [h1]
      have hMdet : M.det ≠ 0 := by
        have hBsnz : (Matrix.fromBlocks G R 0 M).det ≠ 0 := by
          rw [← hBs]
          rwa [Matrix.det_reindex_self e.symm B]
        have hmul : (Matrix.fromBlocks G R 0 M).det = g * M.det := by
          rw [Matrix.det_fromBlocks_zero₂₁]
          simp [G, Matrix.det_unique]
        by_contra hM
        exact hBsnz (by rw [hmul, hM, mul_zero])
      obtain ⟨V, hVunit, hVtri⟩ := ih M hMdet
      let U_sum : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℤ :=
        Matrix.fromBlocks (1 : Matrix Unit Unit ℤ) 0 0 V
      let Ufull : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := reindex e e U_sum
      have hB_eq : B = reindex e e Bs := by
        dsimp [Bs]
        exact (Equiv.apply_symm_apply (reindex e e) B).symm
      have hprod_sum : U_sum * Bs = Matrix.fromBlocks G R 0 (V * M) := by
        rw [hBs]
        dsimp [U_sum]
        rw [Matrix.fromBlocks_multiply]
        simp
      have htri0 : Ufull * B = reindex e e (U_sum * Bs) := by
        dsimp [Ufull]
        calc
          reindex e e U_sum * B = reindex e e U_sum * reindex e e Bs := by rw [hB_eq]
          _ = reindex e e (U_sum * Bs) := by
            symm
            exact (reindexRingEquiv ℤ e).map_mul U_sum Bs
      have hUfullU : IsUnit (reindex e e U_sum).det := by
        rw [Matrix.det_reindex_self e U_sum]
        dsimp [U_sum]
        rw [Matrix.det_fromBlocks_zero₂₁]
        simp [hVunit]
      have hUfull : IsUnit Ufull.det := by
        simpa [Ufull] using hUfullU
      have htriB : ∀ (i j : Fin (n + 1)), j < i → (Ufull * B) i j = 0 := by
        intro i j hij
        rcases Fin.eq_zero_or_eq_succ i with hiz | ⟨i₀, hi⟩
        · subst i
          exfalso
          exact not_lt_fin_zero j hij
        · subst i
          rcases Fin.eq_zero_or_eq_succ j with hjz | ⟨j₀, hj⟩
          · subst j
            rw [htri0, Matrix.reindex_apply, Matrix.submatrix_apply, hprod_sum]
            have h1 : e.symm i₀.succ = Sum.inr i₀ := by simp [e]
            have h2 : e.symm (0 : Fin (n + 1)) = Sum.inl Unit.unit := by simp [e]
            rw [h1, h2]
            rfl
          · subst j
            have hji : j₀ < i₀ := Fin.succ_lt_succ_iff.mp hij
            rw [htri0, Matrix.reindex_apply, Matrix.submatrix_apply, hprod_sum]
            have h1 : e.symm i₀.succ = Sum.inr i₀ := by simp [e]
            have h2 : e.symm j₀.succ = Sum.inr j₀ := by simp [e]
            rw [h1, h2]
            change (V *ᵥ (fun r : Fin n => M r j₀)) i₀ = 0
            exact hVtri i₀ j₀ hji
      refine ⟨Ufull * W, ?_, ?_⟩
      · rw [Matrix.det_mul]
        exact IsUnit.mul hUfull hWunit
      · intro i j hij
        rw [mulVec_col (Ufull * W) A j i]
        have hUA : ((Ufull * W) * A) = Ufull * B := by
          rw [Matrix.mul_assoc]
        rw [hUA]
        exact htriB i j hij

/-- Given an invertible integer matrix `Z` (with columns `z c`), there is a unimodular
integer matrix `U` (i.e. `IsUnit U.det`) so that `U • column c` has support in the first
`c+1` rows for every `c` — equivalently `(U.mulVec (z c)) r = 0` whenever `c < r`.
(This is the existence of an upper-triangular (row-style) Hermite form for the column
reduction of an invertible integer matrix.)

`z : Fin d → (Fin d → ℤ)` lists the columns; the matrix is `Z r c := z c r` with
`det Z ≠ 0`. -/
theorem exists_unimodular_upperTriangular_columns {d : ℕ} (z : Fin d → (Fin d → ℤ))
    (hd : d ≠ 0)
    (hdet : (Matrix.of (fun r : Fin d => fun c : Fin d => z c r)).det ≠ 0) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnit U.det ∧
      ∀ (c r : Fin d), c < r → (U.mulVec (z c)) r = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun r c => z c r)
  obtain ⟨U, hU, htri⟩ := upperTri A hdet
  refine ⟨U, hU, ?_⟩
  intro c r hlt
  simpa [A] using htri r c hlt

end Commons.Data.Matrix
