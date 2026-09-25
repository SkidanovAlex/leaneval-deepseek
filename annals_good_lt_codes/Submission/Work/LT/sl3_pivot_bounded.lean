import Mathlib
import Submission.Work.LT.two_block_diagonal_bounded
import Submission.Work.LT.pivot_reindex_bounded

/-!
# Bounded two-sided pivot reduction

We prove that an `n × n` matrix over a field can be reduced to diagonal form using at most
`0 + 1 + 2 + ⋯ + n` transvections on each side, by mirroring Mathlib's induction
(`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`) while tracking the
lengths of the lists of transvections.  The case `n = 3` gives the statement
`Work.LT.sl3_pivot_bounded` with the (generous) bound `20`.

The two ingredients proved in parallel are
`Work.LT.two_block_diagonal_bounded` (the bounded block-diagonalisation step) and
`Work.LT.pivot_reindex_bounded` (transport of a bounded reduction along a reindexing).
-/

namespace Work.LT

/-- Number of transvections on one side that suffice to diagonalise an `n × n` matrix:
`0 + 1 + 2 + ⋯ + n`. -/
def pivotBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => pivotBound n + (n + 1)

theorem pivotBound_succ (n : ℕ) : pivotBound (n + 1) = pivotBound n + (n + 1) := rfl

/-- For `n = 3` the bound is `1 + 2 + 3 = 6`. -/
theorem pivotBound_three : pivotBound 3 = 6 := by decide

/-- **Induction step of the bounded pivot reduction.** If every `r × r` matrix can be reduced to
diagonal form using at most `pivotBound r` transvections on each side, then the same holds for
`(r+1) × (r+1)` matrices with bound `pivotBound (r+1) = pivotBound r + (r + 1)`:
first put the matrix in two-block-diagonal form (at most `r + 1` transvections per side), then
reduce the `r × r` diagonal block by the induction hypothesis. -/
theorem pivotBlockStep {K : Type*} [Field K] {r : ℕ}
    (IH : ∀ M : Matrix (Fin r) (Fin r) K,
      ∃ (L L' : List (Matrix.TransvectionStruct (Fin r) K)) (D : Fin r → K),
        (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
            (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
          L.length ≤ pivotBound r ∧ L'.length ≤ pivotBound r)
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K) :
    ∃ (L L' : List (Matrix.TransvectionStruct (Fin r ⊕ Unit) K)) (D : Fin r ⊕ Unit → K),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
        L.length ≤ pivotBound (r + 1) ∧ L'.length ≤ pivotBound (r + 1) := by
  obtain ⟨L₁, L₁', h₁, hlen₁, hlen₁'⟩ := two_block_diagonal_bounded M
  let M' := (L₁.map Matrix.TransvectionStruct.toMatrix).prod * M *
    (L₁'.map Matrix.TransvectionStruct.toMatrix).prod
  obtain ⟨L₀, L₀', D₀, h₀, hlen₀, hlen₀'⟩ := IH M'.toBlocks₁₁
  refine ⟨L₀.map (Matrix.TransvectionStruct.sumInl Unit) ++ L₁,
    L₁' ++ L₀'.map (Matrix.TransvectionStruct.sumInl Unit),
    Sum.elim D₀ (fun _ => M' (Sum.inr ()) (Sum.inr ())), ?_, ?_, ?_⟩
  · suffices hh : (L₀.map (Matrix.TransvectionStruct.toMatrix ∘
          Matrix.TransvectionStruct.sumInl Unit)).prod * M' *
        (L₀'.map (Matrix.TransvectionStruct.toMatrix ∘
          Matrix.TransvectionStruct.sumInl Unit)).prod =
          Matrix.diagonal (Sum.elim D₀ fun _ => M' (Sum.inr ()) (Sum.inr ())) by
      simpa [M', Matrix.mul_assoc, List.map_map, Function.comp_def] using hh
    have hM' : M' = Matrix.fromBlocks M'.toBlocks₁₁ 0 0
        (Matrix.diagonal fun _ => M' (Sum.inr ()) (Sum.inr ())) := by
      rw [← Matrix.fromBlocks_toBlocks M', h₁.1, h₁.2]
      rfl
    rw [hM']
    simp [h₀]
  · rw [show pivotBound (r + 1) = pivotBound r + (r + 1) from rfl]
    simp only [List.length_append, List.length_map]
    omega
  · rw [show pivotBound (r + 1) = pivotBound r + (r + 1) from rfl]
    simp only [List.length_append, List.length_map]
    omega

/-- **Bounded two-sided pivot reduction, general size.** Every `n × n` matrix over a field can be
brought to diagonal form by at most `pivotBound n` elementary row operations on the left and
`pivotBound n` on the right. -/
theorem exists_diagonal_pivotBound {K : Type*} [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) :
    ∃ (L L' : List (Matrix.TransvectionStruct (Fin n) K)) (D : Fin n → K),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
        L.length ≤ pivotBound n ∧ L'.length ≤ pivotBound n := by
  suffices h : ∀ cn : ℕ, ∀ M : Matrix (Fin cn) (Fin cn) K,
      ∃ (L L' : List (Matrix.TransvectionStruct (Fin cn) K)) (D : Fin cn → K),
        (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
            (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
          L.length ≤ pivotBound cn ∧ L'.length ≤ pivotBound cn from h n M
  intro cn
  induction cn with
  | zero =>
    intro M
    exact ⟨[], [], fun i => M i i, by ext i j; exact Fin.elim0 i, by simp, by simp⟩
  | succ r IH =>
    intro M
    set e : Fin r ⊕ Unit ≃ Fin (r + 1) := Fintype.equivOfCardEq (by simp) with he
    have hN := pivotBlockStep (K := K) (r := r) IH (Matrix.reindexAlgEquiv K K e.symm M)
    have hfin := pivot_reindex_bounded (K := K) (n := r + 1) (p := Fin r ⊕ Unit) e
      (pivotBound (r + 1)) (Matrix.reindexAlgEquiv K K e.symm M) hN
    have hsymm : Matrix.reindexAlgEquiv K K e (Matrix.reindexAlgEquiv K K e.symm M) = M := by
      rw [← Matrix.symm_reindexAlgEquiv]
      exact AlgEquiv.apply_symm_apply _ _
    simpa [hsymm] using hfin

/-- **Bounded two-sided pivot reduction.** Every `3 × 3` matrix over a field can be brought to
diagonal form by at most `20` elementary row operations on the left and `20` elementary column
operations on the right. Suggested route: mirror Mathlib's `Matrix.Pivot` induction on the block
decomposition `Fin r ⊕ Unit`, but track lengths: `Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero`
gives lists of length exactly `r`, the degenerate case prepends one element (length `r + 1`), and
the induction step adds `r + 1`; the total for size `3` is `1 + 2 + 3 = 6`. -/
theorem sl3_pivot_bounded {K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) K) :
    ∃ (L L' : List (Matrix.TransvectionStruct (Fin 3) K)) (D : Fin 3 → K),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
      L.length ≤ 20 ∧ L'.length ≤ 20 := by
  obtain ⟨L, L', D, hD, hL, hL'⟩ := exists_diagonal_pivotBound 3 M
  exact ⟨L, L', D, hD, le_trans hL (by decide), le_trans hL' (by decide)⟩

end Work.LT
