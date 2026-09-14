import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

set_option linter.style.haveILetI false

open Matrix exteriorPower
open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-!
# Norm of an exterior product of vectors

We prove the standard bound
`‖v₁ ∧ ⋯ ∧ vₖ‖ ≤ ‖v₁‖ · ⋯ · ‖vₖ‖`
for the canonical Euclidean norm on the `k`th exterior power.

The proof goes through the identity
`‖ιMulti ℝ k v‖² = ⟪ιMulti ℝ k v, ιMulti ℝ k v⟫ = det (gram ℝ v)`
and Hadamard's inequality for positive-semidefinite matrices
(the determinant of a positive-semidefinite real matrix is at most the product
of its diagonal entries).
-/

namespace Hadamard

/-- The equivalence splitting `Fin (n+1)` into `PUnit ⊕ Fin n`,
mapping `0 ↦ inl ()` and `j.succ ↦ inr j`. -/
def finSuccSumPUnit (n : ℕ) : Fin (n + 1) ≃ Sum PUnit (Fin n) :=
  (finSuccEquiv n).trans ((Equiv.optionEquivSumPUnit (Fin n)).trans (Equiv.sumComm (Fin n) PUnit))

@[simp] lemma finSuccSumPUnit_zero (n : ℕ) : finSuccSumPUnit n 0 = Sum.inl PUnit.unit := by
  simp [finSuccSumPUnit]

@[simp] lemma finSuccSumPUnit_succ (n : ℕ) (j : Fin n) :
    finSuccSumPUnit n j.succ = Sum.inr j := by
  simp [finSuccSumPUnit]

@[simp] lemma finSuccSumPUnit_symm_inl (n : ℕ) (u : PUnit) :
    (finSuccSumPUnit n).symm (Sum.inl u) = (0 : Fin (n + 1)) := by
  cases u
  simp [finSuccSumPUnit]

@[simp] lemma finSuccSumPUnit_symm_inr (n : ℕ) (j : Fin n) :
    (finSuccSumPUnit n).symm (Sum.inr j) = j.succ := by
  simp [finSuccSumPUnit]

/-- Splitting a matrix indexed by `Fin (n+1)` along the first index `0`. -/
lemma fromBlocks_of_reindex {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Matrix.reindex (finSuccSumPUnit m) (finSuccSumPUnit m) A =
      Matrix.fromBlocks
        (fun _ _ : PUnit => A 0 0)
        (fun (_ : PUnit) (j : Fin m) => A 0 j.succ)
        (fun (j : Fin m) (_ : PUnit) => A j.succ 0)
        (fun (j : Fin m) (k : Fin m) => A j.succ k.succ) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.reindex, Matrix.fromBlocks]

/-- The determinant is invariant under this reindexing. -/
lemma det_reindex_e {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    (Matrix.reindex (finSuccSumPUnit m) (finSuccSumPUnit m) A).det = A.det := by
  exact Matrix.det_reindex_self (finSuccSumPUnit m) A

/-- A Hermitian real matrix is symmetric. -/
lemma isHermitian_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i j : Fin n) :
    A i j = A j i := by
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.conjTranspose] using h.symm

/-- **Hadamard's inequality** for positive-definite real matrices, by induction on the size
using the Schur complement along the first index. -/
lemma posDef_det_le_prod_diag :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef → A.det ≤ ∏ i : Fin n, A i i
  | 0, A, hA => by
      simp
  | m + 1, A, hA => by
      classical
      let D : Matrix (Fin m) (Fin m) ℝ := fun j k => A j.succ k.succ
      let a : Matrix PUnit PUnit ℝ := fun _ _ => A 0 0
      let b : Matrix PUnit (Fin m) ℝ := fun _ j => A 0 j.succ
      let c : Matrix (Fin m) PUnit ℝ := fun j _ => A j.succ 0
      have hD : D.PosDef := by
        dsimp [D]
        exact hA.submatrix (Fin.succ_injective m)
      have hDdet : 0 < D.det := hD.det_pos
      letI : Invertible D.det := invertibleOfNonzero (ne_of_gt hDdet)
      letI : Invertible D := Matrix.invertibleOfDetInvertible D
      have hdet1 :
          (Matrix.reindex (finSuccSumPUnit m) (finSuccSumPUnit m) A).det = A.det := det_reindex_e A
      have hBlocks :
          Matrix.reindex (finSuccSumPUnit m) (finSuccSumPUnit m) A = Matrix.fromBlocks a b c D := by
        ext i j
        cases i <;> cases j <;> simp [Matrix.reindex, Matrix.fromBlocks, a, b, c, D]
      have hdetA : A.det = D.det * (a - b * ⅟D * c).det := by
        rw [← hdet1, hBlocks]
        exact Matrix.det_fromBlocks₂₂ a b c D
      have hsym (i j : Fin (m + 1)) : A i j = A j i := isHermitian_symm A hA.1 i j
      have hc : c = bᴴ := by
        ext j u
        cases u
        change A j.succ 0 = A 0 j.succ
        exact hsym j.succ 0
      let T := a - b * ⅟D * c
      have hTpsd : T.PosSemidef := by
        have hB : (Matrix.fromBlocks a b c D).PosDef := by
          rw [← hBlocks]
          exact Matrix.PosDef.submatrix hA (finSuccSumPUnit m).symm.injective
        have hB' : (Matrix.fromBlocks a b bᴴ D).PosSemidef := by
          simpa [hc] using hB.posSemidef
        have hSchur := (Matrix.PosDef.fromBlocks₂₂ a b hD).mp hB'
        have hinv : ⅟D = D⁻¹ := Matrix.invOf_eq_nonsing_inv D
        simpa [T, hc, hinv] using hSchur
      have hTdet : T.det = T () () := Matrix.det_unique T
      have hx0 : 0 ≤ T.det := hTpsd.det_nonneg
      have hx : T () () ≤ A 0 0 := by
        have hDinv : (⅟D : Matrix (Fin m) (Fin m) ℝ).PosSemidef := by
          simpa [Matrix.invOf_eq_nonsing_inv D] using (Matrix.PosDef.inv hD).posSemidef
        have hbDb : (b * ⅟D * bᴴ : Matrix PUnit PUnit ℝ).PosSemidef :=
          Matrix.PosSemidef.mul_mul_conjTranspose_same hDinv b
        have hdiag : 0 ≤ (b * ⅟D * bᴴ) () () := hbDb.diag_nonneg
        calc
          T () () = a () () - (b * ⅟D * c) () () := rfl
          _ = A 0 0 - (b * ⅟D * c) () () := by simp [a]
          _ = A 0 0 - (b * ⅟D * bᴴ) () () := by rw [hc]
          _ ≤ A 0 0 := by linarith
      have ha0 : 0 ≤ A 0 0 := (hA.diag_pos (i := 0)).le
      have ih : D.det ≤ ∏ j : Fin m, D j j := posDef_det_le_prod_diag m D hD
      have hprod : (∏ i : Fin (m + 1), A i i) = A 0 0 * ∏ j : Fin m, A j.succ j.succ := by
        exact Fin.prod_univ_succ (fun i : Fin (m + 1) => A i i)
      calc
        A.det = D.det * T.det := by simpa [T] using hdetA
        _ ≤ D.det * A 0 0 := mul_le_mul_of_nonneg_left (by simpa [hTdet] using hx) hDdet.le
        _ = A 0 0 * D.det := by ring
        _ ≤ A 0 0 * (∏ j : Fin m, D j j) := mul_le_mul_of_nonneg_left ih ha0
        _ = A 0 0 * ∏ j : Fin m, A j.succ j.succ := by simp [D]
        _ = ∏ i : Fin (m + 1), A i i := by rw [← hprod]

/-- **Hadamard's inequality** for positive-semidefinite real matrices: the determinant is at
most the product of the diagonal entries. -/
lemma det_le_prod_diag_of_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) : A.det ≤ ∏ i : Fin n, A i i := by
  by_cases hne : A.det ≠ 0
  · have hpd : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hne
    exact posDef_det_le_prod_diag n A hpd
  · have hdet : A.det = 0 := not_not.mp hne
    rw [hdet]
    exact Finset.prod_nonneg (fun i _ => hA.diag_nonneg)

end Hadamard

/-- The norm of the exterior product of a family of vectors is bounded by the product of their
norms: `‖v₁ ∧ ⋯ ∧ vₖ‖ ≤ ‖v₁‖ · ⋯ · ‖vₖ‖`. -/
lemma exteriorPower_norm_wedge_le_prod {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ k v‖ ≤ ∏ i : Fin k, ‖v i‖ := by
  have hsq : ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 ≤ (∏ i : Fin k, ‖v i‖) ^ 2 := by
    calc
      ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ k v) (exteriorPower.ιMulti ℝ k v) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ k v)).symm
      _ = (Matrix.gram ℝ v).det := by
        rw [exteriorPower.inner_ιMulti_self]
      _ ≤ ∏ i : Fin k, (Matrix.gram ℝ v) i i := by
        exact Hadamard.det_le_prod_diag_of_posSemidef (A := Matrix.gram ℝ v)
          (Matrix.posSemidef_gram ℝ v)
      _ = ∏ i : Fin k, ‖v i‖ ^ 2 := by
        apply Finset.prod_congr rfl
        intro i _
        simp [Matrix.gram_apply, inner_self_eq_norm_sq_to_K]
      _ = (∏ i : Fin k, ‖v i‖) ^ 2 := by
        rw [Finset.prod_pow]
  have hprodnonneg : 0 ≤ ∏ i : Fin k, ‖v i‖ :=
    Finset.prod_nonneg (fun i _ => norm_nonneg (v i))
  have habs : |‖exteriorPower.ιMulti ℝ k v‖| = ‖exteriorPower.ιMulti ℝ k v‖ :=
    abs_of_nonneg (norm_nonneg _)
  have hprodabs : |∏ i : Fin k, ‖v i‖| = ∏ i : Fin k, ‖v i‖ := abs_of_nonneg hprodnonneg
  rw [← habs, ← hprodabs]
  exact (sq_le_sq.mp (by simpa using hsq))

end Commons.Analysis.InnerProductSpace