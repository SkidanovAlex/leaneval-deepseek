/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stacking a row on top of a matrix

For the finite-descent step of `Work.Section3.rank_diff_of_fp_model_elementwise` one needs the
matrix obtained by stacking a row `u : Fin n → S` underneath an `a × n` matrix `A`, so that the
row space of the result is `rowspace A ⊔ span {u}`.

This file records the construction `stacked` and the elementary facts about it that are used
later: it commutes with `Matrix.map` along a ring homomorphism, the row space of a matrix is the
span of its rows, and consequently the row space of `stacked A u` is the supremum of the row
space of `A` and the span of the row `u`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.Epic.LiDim.RowSpaceToolkit
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_append_le

set_option autoImplicit false
universe u
namespace Work.Section3
open Matrix
open Work.ORHughesFree.Epic (rowMulLin)

def stacked {S : Type u} [Zero S] {a n : ℕ} (A : Matrix (Fin a) (Fin n) S) (u : Fin n → S) :
    Matrix (Fin (a + 1)) (Fin n) S :=
  fun i j => Fin.lastCases (u j) (fun k => A k j) i

theorem stacked_castSucc {S : Type u} [Zero S] {a n : ℕ} (A : Matrix (Fin a) (Fin n) S)
    (u : Fin n → S) (i : Fin a) : stacked A u (Fin.castSucc i) = A i := by
  funext j; simp [stacked]

theorem stacked_last {S : Type u} [Zero S] {a n : ℕ} (A : Matrix (Fin a) (Fin n) S)
    (u : Fin n → S) : stacked A u (Fin.last a) = u := by
  funext j; simp [stacked]

/-- Stacking commutes with the pointwise image along a ring homomorphism. -/
theorem stacked_map {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) {a n : ℕ}
    (A : Matrix (Fin a) (Fin n) R) (v : Fin n → R) :
    (stacked A v).map f = stacked (A.map f) (fun j => f (v j)) := by
  ext i j
  induction i using Fin.lastCases with
  | last => simp [stacked]
  | cast i => simp [stacked]

theorem range_rowMulLin_eq_span_range {S : Type u} [Ring S] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) S) :
    LinearMap.range (rowMulLin A) = Submodule.span S (Set.range (fun i : Fin m => A i)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    have hv : v = ∑ i, v i • (Pi.single i (1 : S) : Fin m → S) :=
      Work.ORHughesFree.Epic.LiDim.eq_sum_smul_single v
    have h2 : rowMulLin A v = ∑ i, v i • A i := by
      conv_lhs => rw [hv]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, Work.ORHughesFree.Epic.LiDim.rowMulLin_single]
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact ⟨Pi.single i 1, Work.ORHughesFree.Epic.LiDim.rowMulLin_single A i⟩

theorem range_rowMulLin_stacked {S : Type u} [Ring S] {a n : ℕ} (A : Matrix (Fin a) (Fin n) S)
    (u : Fin n → S) :
    LinearMap.range (rowMulLin (stacked A u))
      = LinearMap.range (rowMulLin A) ⊔ Submodule.span S ({u} : Set (Fin n → S)) := by
  rw [range_rowMulLin_eq_span_range, range_rowMulLin_eq_span_range]
  have hrange : Set.range (fun i : Fin (a + 1) => stacked A u i)
      = Set.range (fun i : Fin a => A i) ∪ {u} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | hlast
      · exact Or.inl ⟨k, (stacked_castSucc A u k).symm⟩
      · rw [hlast]
        exact Or.inr (stacked_last A u)
    · intro hx
      rcases hx with ⟨k, hk⟩ | hx
      · refine ⟨Fin.castSucc k, ?_⟩
        show stacked A u (Fin.castSucc k) = x
        rw [stacked_castSucc]
        simpa using hk
      · rw [Set.mem_singleton_iff] at hx
        refine ⟨Fin.last a, ?_⟩
        show stacked A u (Fin.last a) = x
        rw [stacked_last, ← hx]
  rw [hrange, Submodule.span_union]

end Work.Section3
