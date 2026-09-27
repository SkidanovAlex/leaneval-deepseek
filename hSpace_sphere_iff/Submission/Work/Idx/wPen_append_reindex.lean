import Mathlib
import Submission.Work.Idx.WPenAppendDefs

namespace Work.Idx

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {n d : ℕ}

set_option linter.unusedSectionVars false

/-! ## Entry computations for the append reindexing

The equivalence `eb n d : (WIdx n d) ⊕ Fin n ≃ Fin (d+2) × Fin n` sends the block
`(a, y)` of the `(d+1)`-block W pencil to the block `(Fin.castSucc a, y)` of the
`(d+2)`-block pencil, and the extra summand `Fin n` to the last block `d+1`. The
lemmas below record this on entries, in the form used to compare the block form
`Ablk`/`Bblk` of the `(d+2)`-block pencil with the W pencil's own matrices. -/

lemma eb_symm_of_lt (i : Fin (d + 2) × Fin n) (h : (i.1 : ℕ) < d + 1) :
    (eb n d).symm i = Sum.inl (⟨i.1, h⟩, i.2) := by
  rw [Equiv.symm_apply_eq, eb_inl]
  exact Prod.ext (Fin.ext rfl) rfl

lemma eb_symm_of_not_lt (i : Fin (d + 2) × Fin n) (h : ¬ (i.1 : ℕ) < d + 1) :
    (eb n d).symm i = Sum.inr i.2 := by
  have hle : (i.1 : ℕ) = d + 1 := by have := i.1.isLt; omega
  have hi : i.1 = lastIdx d := by apply Fin.ext; simp [lastIdx, hle]
  rw [Equiv.symm_apply_eq, eb_inr, ← hi]

/-- The last block row of `wPenB X n d b` is the row of coefficient matrices. -/
lemma rowb_apply_fin (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (x : Fin n)
    (a : Fin (d + 1)) (y : Fin n) : rowb X n d b x (a, y) = b a x y := by
  rw [rowb_apply, wPenB_apply]
  rw [if_neg (by intro hc; have := a.isLt; simp only [dIdx_val] at hc; omega)]
  simp [dIdx_val]

/-- The reindexed `Ablk` is the `(d+2)`-block `z`-coefficient `wPenA`: the identity in every
block except the last. -/
lemma reindex_Ablk_apply (i j : Fin (d + 2) × Fin n) :
    Matrix.reindex (eb n d) (eb n d) (Ablk X n d) i j
      = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d + 1
          then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2 else 0 := by
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases h : (i1 : ℕ) < d + 1
  · rw [eb_symm_of_lt _ h]
    by_cases h' : (j1 : ℕ) < d + 1
    · rw [eb_symm_of_lt _ h']
      simp only [Ablk, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Prod.mk.injEq, Fin.mk.injEq]
      have hne : (i1 : ℕ) ≠ d + 1 := by omega
      by_cases hij : i1 = j1 <;> by_cases h2 : i2 = j2 <;> simp_all [Fin.ext_iff]
    · rw [eb_symm_of_not_lt _ h']
      simp only [Ablk, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      have hnot : ¬(i1 = j1 ∧ (i1:ℕ) ≠ d+1) := by
        rintro ⟨hij, -⟩
        exact h' (by rw [← hij]; exact h)
      rw [if_neg hnot]
  · rw [eb_symm_of_not_lt _ h]
    by_cases h' : (j1 : ℕ) < d + 1
    · rw [eb_symm_of_lt _ h']
      simp only [Ablk, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      have hnot : ¬(i1 = j1 ∧ (i1:ℕ) ≠ d+1) := by
        rintro ⟨hij, -⟩
        have hi : (i1:ℕ) = d + 1 := by have := i1.isLt; omega
        have hj : (j1:ℕ) = d + 1 := by rw [← hij]; exact hi
        omega
      rw [if_neg hnot]
    · rw [eb_symm_of_not_lt _ h']
      simp only [Ablk, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      have hnot : ¬(i1 = j1 ∧ (i1:ℕ) ≠ d+1) := by
        rintro ⟨-, hne⟩
        exact hne (by have := i1.isLt; omega)
      rw [if_neg hnot]

/-- The reindexed `Bblk` is the `(d+2)`-block constant part `wPenB` of the appended coefficient
sequence: the block form of the companion pencil. -/
lemma reindex_Bblk_apply (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (i j : Fin (d + 2) × Fin n) :
    Matrix.reindex (eb n d) (eb n d) (Bblk X n d b) i j
      = (if (i.1:ℕ)+1 = (j.1:ℕ) then
           (if (i.1:ℕ) = d+1 then Work.KT.Idx.appSeq X b j.1 i.2 j.2
             else -(1 : Matrix (Fin n) (Fin n) C(X,ℂ)) i.2 j.2)
         else if (i.1:ℕ) = d+1 then Work.KT.Idx.appSeq X b j.1 i.2 j.2 else 0) := by
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases h : (i1 : ℕ) < d + 1
  · rw [eb_symm_of_lt _ h]
    by_cases h' : (j1 : ℕ) < d + 1
    · rw [eb_symm_of_lt _ h']
      simp only [Bblk, Matrix.fromBlocks_apply₁₁, BBl_apply]
      have hne : (i1:ℕ) ≠ d+1 := by omega
      by_cases hc : (i1:ℕ)+1 = (j1:ℕ) <;> simp_all
    · rw [eb_symm_of_not_lt _ h']
      simp only [Bblk, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Ecol_apply]
      have hj : (j1:ℕ) = d+1 := by have := j1.isLt; omega
      have hne : (i1:ℕ) ≠ d+1 := by omega
      have hfe : ((⟨(i1:ℕ), h⟩ : Fin (d+1)) = dIdx d) ↔ ((i1:ℕ) = d) := by
        rw [Fin.ext_iff]; simp [dIdx_val]
      simp only [hfe]
      rw [hj]
      rw [if_neg hne, if_neg hne]
      by_cases hd : (i1:ℕ) = d
      · rw [if_pos (show (i1:ℕ)+1 = d+1 by omega)]
        by_cases h2 : i2 = j2 <;> simp_all [Matrix.one_apply]
      · rw [if_neg (show ¬((i1:ℕ)+1 = d+1) by omega)]
        simp [hd]
  · rw [eb_symm_of_not_lt _ h]
    by_cases h' : (j1 : ℕ) < d + 1
    · rw [eb_symm_of_lt _ h']
      simp only [Bblk, Matrix.fromBlocks_apply₂₁, rowb_apply_fin]
      have hi : (i1:ℕ) = d+1 := by have := i1.isLt; omega
      rw [if_neg (by omega), if_pos hi]
      rw [Work.KT.Idx.appSeq_apply, dif_pos h']
    · rw [eb_symm_of_not_lt _ h']
      simp only [Bblk, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      have hi : (i1:ℕ) = d+1 := by have := i1.isLt; omega
      rw [if_neg (by omega), if_pos hi]
      rw [Work.KT.Idx.appSeq_apply, dif_neg (by omega)]
      simp

theorem wPen_append_reindex (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Matrix.reindex (Work.Idx.eb n d) (Work.Idx.eb n d) (Work.Idx.Ablk X n d)
        = Work.KT.Idx.wPenA X n (d + 1)) ∧
    (Matrix.reindex (Work.Idx.eb n d) (Work.Idx.eb n d) (Work.Idx.Bblk X n d b)
        = Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b)) := by
  constructor
  · ext i j
    rw [reindex_Ablk_apply, wPenA_apply]
  · ext i j
    rw [reindex_Bblk_apply, wPenB_apply]

end

end Work.Idx
