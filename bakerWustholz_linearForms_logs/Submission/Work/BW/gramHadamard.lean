import Mathlib
import Submission.Work.BW.schurPosSemidef
import Submission.Work.BW.psdDiagZero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hadamard's inequality for Gram matrices

`gramHadamard`: for a real `m × n` matrix `B`, the determinant of the Gram matrix `B * Bᵀ` of
its rows is at most the product of the squared Euclidean norms of the rows.

This is Hadamard's determinant inequality applied to the positive semidefinite matrix `B * Bᵀ`,
whose diagonal entries are the squared row norms.  We prove the general statement
`gramHadamard_posSemidef` (the determinant of a positive semidefinite real matrix is at most the
product of its diagonal entries) by strong induction on the dimension, peeling off one index with
the Schur complement.
-/

namespace Work.BW

open Matrix

/-- A square matrix reindexed along `Equiv.sumCompl p` coincides with the `fromBlocks` matrix
built from its four blocks. -/
lemma gramHadamard_submatrix_sumCompl_toBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (p : ι → Prop) [DecidablePred p] :
    A.submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
      Matrix.fromBlocks (A.toBlock p p) (A.toBlock p (fun i => ¬p i))
        (A.toBlock (fun i => ¬p i) p) (A.toBlock (fun i => ¬p i) (fun i => ¬p i)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [Matrix.toBlock_apply, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
          Matrix.submatrix_apply]

/-- The product of the diagonal entries splits along a single distinguished index `i₀`, the
complement being described by the corresponding `toBlock`. -/
lemma gramHadamard_prod_diag_split {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (P : ι → Prop) [DecidablePred P] (i₀ : ι) (hP : P i₀) (hPu : ∀ i, P i → i = i₀) :
    ∏ i, A i i = A i₀ i₀ *
      ∏ i : {i // ¬P i}, (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) i i := by
  classical
  rw [Fintype.prod_equiv (Equiv.sumCompl P).symm (fun i => A i i)
        (fun x => A ((Equiv.sumCompl P) x) ((Equiv.sumCompl P) x)) (fun i => by simp)]
  rw [Fintype.prod_sum_type]
  haveI : Unique {i // P i} := ⟨⟨⟨i₀, hP⟩⟩, fun a => Subtype.ext (hPu a.val a.property)⟩
  have h1 : ∏ x : {i // P i}, A ((Equiv.sumCompl P) (Sum.inl x))
        ((Equiv.sumCompl P) (Sum.inl x)) = A i₀ i₀ := by
    rw [Fintype.prod_unique, Equiv.sumCompl_apply_inl,
        show (default : {i // P i}).val = i₀ from hPu _ (default : {i // P i}).property]
  have h2 : ∏ x : {i // ¬P i}, A ((Equiv.sumCompl P) (Sum.inr x))
        ((Equiv.sumCompl P) (Sum.inr x))
      = ∏ i : {i // ¬P i}, (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) i i := by
    apply Finset.prod_congr rfl
    intro x _
    rw [Equiv.sumCompl_apply_inr, Matrix.toBlock_apply]
  rw [h1, h2]

/-- **Hadamard's inequality for positive semidefinite matrices** (strong induction on the
dimension). The determinant of a positive semidefinite real matrix is at most the product of its
diagonal entries. -/
theorem gramHadamard_posSemidef_aux (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ (A : Matrix ι ι ℝ), A.PosSemidef → A.det ≤ ∏ i, A i i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hcard A hA
    rcases isEmpty_or_nonempty ι with hι | hi₀
    · haveI := hι
      simp [Matrix.det_isEmpty]
    · obtain ⟨i₀⟩ := hi₀
      classical
      by_cases ha : A i₀ i₀ = 0
      · -- the `i₀`-th row vanishes, so the determinant is `0`
        have hrow := psdDiagZero A hA ha
        rw [Matrix.det_eq_zero_of_row_eq_zero i₀ hrow]
        exact Finset.prod_nonneg (fun i _ => hA.diag_nonneg)
      · have hapos : 0 < A i₀ i₀ := lt_of_le_of_ne hA.diag_nonneg (Ne.symm ha)
        let P : ι → Prop := fun i => i = i₀
        -- the `(i₀,i₀)` principal block and its determinant
        have hA11psd : (A.toBlock P P).PosSemidef :=
          hA.submatrix (fun x : {i // P i} => x.val)
        have hA11det : (A.toBlock P P).det = A i₀ i₀ := by
          rw [Matrix.det_unique, Matrix.toBlock_apply]
          congr 2
        have hunit : IsUnit (A.toBlock P P).det := by
          rw [hA11det]; exact isUnit_iff_ne_zero.mpr ha
        haveI : Invertible (A.toBlock P P) := Matrix.invertibleOfIsUnitDet _ hunit
        -- the Schur complement
        let Schur : Matrix {i // ¬P i} {i // ¬P i} ℝ :=
          (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) - (A.toBlock (fun i => ¬P i) P)
            * ⅟(A.toBlock P P) * (A.toBlock P (fun i => ¬P i))
        have hM : (Matrix.fromBlocks (A.toBlock P P) (A.toBlock P (fun i => ¬P i))
              (A.toBlock (fun i => ¬P i) P)
              (A.toBlock (fun i => ¬P i) (fun i => ¬P i))).PosSemidef := by
          rw [← gramHadamard_submatrix_sumCompl_toBlock A P]
          exact hA.submatrix (Equiv.sumCompl P)
        have hSchurPSD : Schur.PosSemidef := schurPosSemidef hM
        have hcard' : Fintype.card {i // ¬P i} < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (p := fun i => ¬P i) (x := i₀) (by simp [P])
        have ihSchur : Schur.det ≤ ∏ i, Schur i i :=
          ih (Fintype.card {i // ¬P i}) hcard' rfl Schur hSchurPSD
        -- diagonal entries of the Schur complement are bounded by those of the block
        have hle : ∀ i : {i // ¬P i},
            Schur i i ≤ (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) i i := by
          intro i
          have hX : 0 ≤ ((A.toBlock (fun i => ¬P i) P) * ⅟(A.toBlock P P)
                * (A.toBlock P (fun i => ¬P i))) i i := by
            have hinv : (⅟(A.toBlock P P)).PosSemidef := by
              rw [Matrix.invOf_eq_nonsing_inv]; exact hA11psd.inv
            have hconj :=
              Matrix.PosSemidef.mul_mul_conjTranspose_same hinv (A.toBlock (fun i => ¬P i) P)
            have hCT : (A.toBlock (fun i => ¬P i) P).conjTranspose
                = A.toBlock P (fun i => ¬P i) := by
              ext a b
              simp only [Matrix.conjTranspose_apply, Matrix.toBlock_apply]
              simpa using hA.isHermitian.apply a.val b.val
            rw [hCT] at hconj
            exact hconj.diag_nonneg
          simp only [Schur, Matrix.sub_apply]
          linarith
        have hprod : ∏ i, Schur i i
            ≤ ∏ i, (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) i i :=
          Finset.prod_le_prod₀ (fun i _ => hSchurPSD.diag_nonneg) (fun i _ => hle i)
        have hdetA : A.det = (A.toBlock P P).det * Schur.det := by
          rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCompl P) A,
              gramHadamard_submatrix_sumCompl_toBlock A P, Matrix.det_fromBlocks₁₁]
        calc A.det = (A.toBlock P P).det * Schur.det := hdetA
          _ ≤ (A.toBlock P P).det
                * ∏ i, (A.toBlock (fun i => ¬P i) (fun i => ¬P i)) i i := by
              rw [hA11det]
              exact mul_le_mul_of_nonneg_left (le_trans ihSchur hprod) (le_of_lt hapos)
          _ = ∏ i, A i i := by
              rw [hA11det, gramHadamard_prod_diag_split A P i₀ rfl (fun i hi => hi)]

/-- **Hadamard's inequality for positive semidefinite matrices.** -/
theorem gramHadamard_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i :=
  gramHadamard_posSemidef_aux _ rfl A hA

/-- **Hadamard's inequality for the Gram matrix of the rows of a real matrix.** -/
theorem gramHadamard {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    (B * B.transpose).det ≤ ∏ i, ∑ j, (B i j) ^ 2 := by
  have hpsd : (B * B.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose B
  have hdiag : ∀ i, (B * B.transpose) i i = ∑ j, (B i j) ^ 2 := by
    intro i
    simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
  calc (B * B.transpose).det ≤ ∏ i, (B * B.transpose) i i := gramHadamard_posSemidef _ hpsd
    _ = ∏ i, ∑ j, (B i j) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i _
        exact hdiag i

end Work.BW
