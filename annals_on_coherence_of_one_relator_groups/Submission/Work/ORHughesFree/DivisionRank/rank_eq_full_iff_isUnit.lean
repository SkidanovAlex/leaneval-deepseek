import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.Faithful.isFaithful_iff
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl

namespace Work.ORHughesFree.DivisionRank

open Work.ORHughesFree

/-- A square matrix over a von Neumann regular ring which has maximal rank `n` is invertible.

Given a faithful Sylvester matrix rank function `rk` on a von Neumann regular ring `U`, a
square matrix `A` over `U` is invertible exactly when `rk A` is maximal (the lemma recorded as
`faithreg` in [JZLA20, §2.4]).  The proof
follows the paper: a weak inverse `B` of `A` (which exists since `Mat_n U` is regular whenever
`U` is) makes `A * B` and `B * A` idempotent with maximal rank `n`; the idempotent complement
identity `rk p + rk (1 - p) = n` then forces `1 - A * B = 0` and `1 - B * A = 0` by
faithfulness. -/
theorem rank_eq_full_iff_isUnit {U : Type*} [Ring U] [VonNeumannRegularRing U]
    (rk : SylvesterRank U) (hfaith : ∀ a : U, rk.rk 1 1 (oneByOne a) = 0 → a = 0)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) U) : IsUnit A ↔ rk.rk n n A = n := by
  constructor
  · intro hA
    have hone := RankAPI.rk_one_fin rk n
    have hle : rk.rk n n A ≤ (n : ℝ) := by
      have h := rk.rk_mul_le_right A (1 : Matrix (Fin n) (Fin n) U)
      rw [Matrix.mul_one] at h
      rwa [hone] at h
    have hge : (n : ℝ) ≤ rk.rk n n A := by
      have h := rk.rk_mul_le_right
        (((hA.unit⁻¹ : (Matrix (Fin n) (Fin n) U)ˣ) : Matrix (Fin n) (Fin n) U)) A
      rw [IsUnit.val_inv_mul hA, hone] at h
      exact h
    linarith
  · intro hrk
    -- `Mat_n U` is von Neumann regular whenever `U` is, so `A` has a weak inverse.
    obtain ⟨B, hB⟩ := (StarRegular.vonNeumannRegularRing_matrix (U := U) n).exists_mul_inverse A
    have hp : (A * B) * (A * B) = A * B := by
      rw [← Matrix.mul_assoc (A * B) A B, hB]
    have hq : (B * A) * (B * A) = B * A := by
      rw [← Matrix.mul_assoc (B * A) B A, Matrix.mul_assoc B A B, Matrix.mul_assoc B (A * B) A, hB]
    have hrkAB : rk.rk n n (A * B) = (n : ℝ) := by
      refine le_antisymm ?_ ?_
      · have h := rk.rk_mul_le_left A B
        rw [hrk] at h
        exact h
      · have h := rk.rk_mul_le_left (A * B) A
        rw [hB, hrk] at h
        exact h
    have hrkBA : rk.rk n n (B * A) = (n : ℝ) := by
      refine le_antisymm ?_ ?_
      · have h := rk.rk_mul_le_right B A
        rw [hrk] at h
        exact h
      · have h := rk.rk_mul_le_right A (B * A)
        have hA2 : A * (B * A) = A := by rw [← Matrix.mul_assoc, hB]
        rw [hA2, hrk] at h
        exact h
    have hAB : A * B = 1 := by
      have hzero : rk.rk n n ((1 : Matrix (Fin n) (Fin n) U) - A * B) = 0 := by
        have h := rk_idempotent_add_compl rk (A * B) hp
        rw [hrkAB] at h
        linarith
      have h1z : (1 : Matrix (Fin n) (Fin n) U) - A * B = 0 := by
        by_contra hne
        exact (Faithful.isFaithful_iff rk).mp hfaith n n _ hne hzero
      exact (sub_eq_zero.mp h1z).symm
    have hBA : B * A = 1 := by
      have hzero : rk.rk n n ((1 : Matrix (Fin n) (Fin n) U) - B * A) = 0 := by
        have h := rk_idempotent_add_compl rk (B * A) hq
        rw [hrkBA] at h
        linarith
      have h1z : (1 : Matrix (Fin n) (Fin n) U) - B * A = 0 := by
        by_contra hne
        exact (Faithful.isFaithful_iff rk).mp hfaith n n _ hne hzero
      exact (sub_eq_zero.mp h1z).symm
    exact isUnit_iff_exists.mpr ⟨B, hAB, hBA⟩

end Work.ORHughesFree.DivisionRank
