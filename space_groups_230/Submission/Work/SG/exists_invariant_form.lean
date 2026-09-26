import Mathlib
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.int_conj_sum_invariant
import Submission.Work.SG.qf_sum_transpose_mul_eq

namespace Work.SG

open scoped Matrix

/-- A finite subgroup `P ≤ GL₃(ℤ)` has a symmetric positive definite `P`-invariant integer form
`Q = ∑_{A ∈ P} AᵀA`.

Route: take `Q := ∑ A ∈ hP.1.toFinset, A.transpose * A`.  Symmetry is termwise.  For `A ∈ P` the
map `B ↦ A * B` is a bijection of `P` onto itself (it is injective because `A` is invertible, and
`P` is finite), which gives `Aᵀ Q A = Q` by reindexing the sum.  Finally
`qf Q v = ∑_{A ∈ P} ∑ i, ((A.mulVec v) i)^2 ≥ ∑ i, (v i)^2 ≥ 0`, and `> 0` for `v ≠ 0`, since
`1 ∈ P` and an integer vector with sum of squares `0` is `0`.  Note `hP` does not directly give
`A⁻¹ ∈ P`: derive that `A ∈ P → ∃ k, A^k = 1` from finiteness (of the powers of `A`) and `IsUnit`
of the determinant. -/
theorem exists_invariant_form (P : Set IMat) (hP : IsIntPointGroup P) :
    ∃ Q : IMat, Q.transpose = Q ∧ (∀ A ∈ P, A.transpose * Q * A = Q) ∧
      (∀ v : IVec, 0 ≤ qf Q v) ∧ (∀ v : IVec, v ≠ 0 → 0 < qf Q v) := by
  classical
  obtain ⟨hfin, h1, hmul, hunit⟩ := hP
  refine ⟨∑ B ∈ hfin.toFinset, B.transpose * B, ?_, ?_, ?_, ?_⟩
  · -- symmetry, termwise
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun B _ => by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · -- invariance under `Q ↦ Aᵀ Q A`, by reindexing `B ↦ B * A`
    intro A hA
    exact int_conj_sum_invariant hfin.toFinset
      (fun A hA B hB => hfin.mem_toFinset.mpr
        (hmul A (hfin.mem_toFinset.mp hA) B (hfin.mem_toFinset.mp hB)))
      (fun A hA => hunit A (hfin.mem_toFinset.mp hA)) A (hfin.mem_toFinset.mpr hA)
  · -- nonnegativity: a sum of squares
    intro v
    rw [qf_sum_transpose_mul_eq]
    exact Finset.sum_nonneg fun B _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  · -- strict positivity, using the summand indexed by `1 ∈ P`
    intro v hv
    have h1S : (1 : IMat) ∈ hfin.toFinset := hfin.mem_toFinset.mpr h1
    rw [qf_sum_transpose_mul_eq]
    have hterm : ∀ B ∈ hfin.toFinset, 0 ≤ ∑ i, (B.mulVec v i)^2 :=
      fun B _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hle := Finset.single_le_sum hterm h1S
    have hobt : ∃ i : Fin 3, v i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hv (funext h)
    have hpos : 0 < ∑ i, ((1 : IMat).mulVec v i)^2 := by
      rw [Matrix.one_mulVec]
      obtain ⟨i, hi⟩ := hobt
      exact Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    exact lt_of_lt_of_le hpos hle

end Work.SG
