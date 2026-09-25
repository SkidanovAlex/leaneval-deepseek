import Mathlib

/-!
# Bounded reduction to two-block-diagonal form

Mathlib's `Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec` shows that
any `(r+1) × (r+1)` matrix over a field can be made two-block-diagonal (blocks `Fin r` and `Unit`)
by multiplying with two lists of transvections, but it gives no control on the lengths of those
lists.  Here we redo the construction of Mathlib's proof while *tracking the lengths*: in every
case the two lists have length at most `r + 1`.

The proof follows `Matrix/LinearAlgebra/Matrix/Transvection.lean` closely:

* if the last coefficient `M (inr ()) (inr ())` is nonzero, then the lists
  `Matrix.Pivot.listTransvecCol M` and `Matrix.Pivot.listTransvecRow M` (both of length `r`) kill
  the last column and the last row;
* otherwise, if `M` is not already two-block-diagonal, one nonzero off-diagonal coefficient in the
  last row or last column can be moved to the `(inr (), inr ())` position with a single extra
  transvection, reducing to the previous case.
-/

namespace Work.LT

open Matrix

/-- If the bottom right coefficient is nonzero, the matrix can be made two-block-diagonal by `r`
transvections on each side. -/
theorem two_block_diagonal_of_ne_zero_bounded {K : Type*} [Field K] {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K)
    (hM : M (Sum.inr ()) (Sum.inr ()) ≠ 0) :
    ∃ L L' : List (Matrix.TransvectionStruct (Fin r ⊕ Unit) K),
      Matrix.IsTwoBlockDiagonal ((L.map Matrix.TransvectionStruct.toMatrix).prod * M *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod) ∧ L.length = r ∧ L'.length = r := by
  let L : List (Matrix.TransvectionStruct (Fin r ⊕ Unit) K) :=
    List.ofFn fun i : Fin r =>
      ⟨Sum.inl i, Sum.inr (), by simp, -M (Sum.inl i) (Sum.inr ()) / M (Sum.inr ()) (Sum.inr ())⟩
  let L' : List (Matrix.TransvectionStruct (Fin r ⊕ Unit) K) :=
    List.ofFn fun i : Fin r =>
      ⟨Sum.inr (), Sum.inl i, by simp, -M (Sum.inr ()) (Sum.inl i) / M (Sum.inr ()) (Sum.inr ())⟩
  refine ⟨L, L', ?_, ?_, ?_⟩
  · have A : L.map Matrix.TransvectionStruct.toMatrix = Matrix.Pivot.listTransvecCol M := by
      simp [L, Matrix.Pivot.listTransvecCol, Function.comp_def]
    have B : L'.map Matrix.TransvectionStruct.toMatrix = Matrix.Pivot.listTransvecRow M := by
      simp [L', Matrix.Pivot.listTransvecRow, Function.comp_def]
    rw [A, B]
    exact Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM
  · simp [L]
  · simp [L']

theorem two_block_diagonal_bounded {K : Type*} [Field K] {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K) :
    ∃ L L' : List (Matrix.TransvectionStruct (Fin r ⊕ Unit) K),
      Matrix.IsTwoBlockDiagonal
          ((L.map Matrix.TransvectionStruct.toMatrix).prod * M *
            (L'.map Matrix.TransvectionStruct.toMatrix).prod) ∧
        L.length ≤ r + 1 ∧ L'.length ≤ r + 1 := by
  by_cases H : Matrix.IsTwoBlockDiagonal M
  · exact ⟨[], [], by simpa using H, by simp, by simp⟩
  by_cases hM : M (Sum.inr ()) (Sum.inr ()) = 0
  · -- `M` is not two-block-diagonal and its bottom right coefficient is zero: some other
    -- coefficient in the last row or in the last column is nonzero.
    have hne : (∃ i : Fin r, M (Sum.inl i) (Sum.inr ()) ≠ 0) ∨
        (∃ i : Fin r, M (Sum.inr ()) (Sum.inl i) ≠ 0) := by
      have h := H
      rw [Matrix.IsTwoBlockDiagonal] at h
      rcases not_and_or.mp h with h | h
      · left
        by_contra h'
        push Not at h'
        exact h (by
          ext i u
          rw [show u = () from Subsingleton.elim u ()]
          simpa [Matrix.toBlocks₁₂] using h' i)
      · right
        by_contra h'
        push Not at h'
        exact h (by
          ext u i
          rw [show u = () from Subsingleton.elim u ()]
          simpa [Matrix.toBlocks₂₁] using h' i)
    rcases hne with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- move the nonzero coefficient `M (inl i) (inr ())` to the bottom right corner
      let T : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K :=
        Matrix.transvection (Sum.inr ()) (Sum.inl i) 1
      let t : Matrix.TransvectionStruct (Fin r ⊕ Unit) K :=
        ⟨Sum.inr (), Sum.inl i, by simp, (1 : K)⟩
      have hTu : (T * M) (Sum.inr ()) (Sum.inr ()) ≠ 0 := by
        rw [show (T * M) (Sum.inr ()) (Sum.inr ()) = M (Sum.inl i) (Sum.inr ()) from by
          simp [T, hM]]
        exact hi
      obtain ⟨L, L', hLL', hL, hL'⟩ := two_block_diagonal_of_ne_zero_bounded (T * M) hTu
      refine ⟨L ++ [t], L', ?_, ?_, ?_⟩
      · have hp : ((L ++ [t]).map Matrix.TransvectionStruct.toMatrix).prod
            = (L.map Matrix.TransvectionStruct.toMatrix).prod * T := by
          simp [t, T]
        rw [hp, Matrix.mul_assoc (L.map Matrix.TransvectionStruct.toMatrix).prod T M]
        exact hLL'
      · simp [hL]
      · simp [hL']
    · -- move the nonzero coefficient `M (inr ()) (inl i)` to the bottom right corner
      let T : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K :=
        Matrix.transvection (Sum.inl i) (Sum.inr ()) 1
      let t : Matrix.TransvectionStruct (Fin r ⊕ Unit) K :=
        ⟨Sum.inl i, Sum.inr (), by simp, (1 : K)⟩
      have hTu : (M * T) (Sum.inr ()) (Sum.inr ()) ≠ 0 := by
        rw [show (M * T) (Sum.inr ()) (Sum.inr ()) = M (Sum.inr ()) (Sum.inl i) from by
          simp [T, hM]]
        exact hi
      obtain ⟨L, L', hLL', hL, hL'⟩ := two_block_diagonal_of_ne_zero_bounded (M * T) hTu
      refine ⟨L, t :: L', ?_, ?_, ?_⟩
      · have hp : ((t :: L').map Matrix.TransvectionStruct.toMatrix).prod
            = T * (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
          simp [t, T]
        rw [hp, ← Matrix.mul_assoc ((L.map Matrix.TransvectionStruct.toMatrix).prod * M) T
          (L'.map Matrix.TransvectionStruct.toMatrix).prod,
          Matrix.mul_assoc (L.map Matrix.TransvectionStruct.toMatrix).prod M T]
        exact hLL'
      · simp [hL]
      · simp [hL']
  · -- the bottom right coefficient is nonzero
    obtain ⟨L, L', hLL', hL, hL'⟩ := two_block_diagonal_of_ne_zero_bounded M hM
    exact ⟨L, L', hLL', by omega, by omega⟩

end Work.LT
