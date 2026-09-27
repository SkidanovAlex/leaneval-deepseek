import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poBdReg
import Submission.Work.Mostow.poActCont
import Submission.Work.Mostow.poContDescent
import Submission.Work.Mostow.hypIsometry

/-!
# Areas T1 and T2 in dimension `0`

This file proves the two area `Prop`s `POActionProp` and `HypIsometryProp` in the degenerate
dimension `n = 0`, which the dimension-`≥ 3` statements `Work.Mostow.poAction` and
`Work.Mostow.hypIsometry` do not cover.

In dimension `0` the chart `E 0 = EuclideanSpace ℝ (Fin 0)` is a subsingleton, so
every clause of the two Props that mentions points of `E 0` is trivial, and the boundary
sphere `Sph 0` (the unit sphere of a one-point space) is empty, which makes the four boundary
clauses vacuous.  The only genuine content is the classification of the orthogonal group
`O(0,1)`: its elements are `1 × 1`-matrices preserving the form `diag(-1)`, so `O(0,1) = {±1}`;
in particular `O(0,1)` is abelian and its centre is everything, whence the projective group
`PO(0,1) = O(0,1)/{±1}` is trivial.

The remaining, non-degenerate clauses (joint continuity of the action, and continuity and
measurability of the boundary action) are supplied by the already proved general lemmas
`poContDescent`, `poActCont` and `poBdReg_PO`, none of which carries a dimension hypothesis.

For `HypIsometryProp` we use the dimension-free theorem `Work.Mostow.hypIsometryAll`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### `O(0,1) = {±1}` -/

/-- In dimension `0` the index type `Fin 0 ⊕ Fin 1` has a single element (the time coordinate),
so the form matrix `J = pmOneMat` is the `1 × 1`-matrix with entry `-1`. -/
lemma pmOneMat_zero :
    (pmOneMat : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℝ) =
      Matrix.diagonal (fun _ => (-1 : ℝ)) := by
  ext c d
  obtain rfl : c = Sum.inr 0 := Subsingleton.elim c _
  obtain rfl : d = Sum.inr 0 := Subsingleton.elim d _
  simp [pmOneMat, Matrix.diagonal]

/-- In dimension `0` a matrix is determined by its single entry, the `(time, time)`-entry. -/
lemma mat_zero_eq_diagonal (A : O1 0) :
    mat A = Matrix.diagonal
      (fun _ : Fin 0 ⊕ Fin 1 => mat A (Sum.inr 0) (Sum.inr 0)) := by
  ext c d
  obtain rfl : c = Sum.inr 0 := Subsingleton.elim c _
  obtain rfl : d = Sum.inr 0 := Subsingleton.elim d _
  simp [Matrix.diagonal]

/-- The underlying-matrix map is injective, in the only dimension where we need it here. -/
lemma mat_injective_zero {A B : O1 0} (h : mat A = mat B) : A = B :=
  Subtype.ext (MatrixSum.ofMatrix.symm.injective h)

/-- The identity of `O(0,1)` has identity matrix. -/
lemma mat_one_zero : mat (1 : O1 0) = 1 := by simp [mat]

/-- Classification of `O(0,1)`: the orthogonal group of the one-dimensional form `diag(-1)` is
`{±1}`. -/
lemma O1_zero_eq_one_or_neg_one (A : O1 0) : A = 1 ∨ A = -1 := by
  have hmat_const := mat_zero_eq_diagonal A
  set e := mat A (Sum.inr 0) (Sum.inr 0) with he
  -- the defining relation `(mat A)ᵀ J (mat A) = J` forces the single entry of `mat A` to be ±1
  have hesq : e ^ 2 = 1 := by
    have hcol := O1_form_col A
    rw [hmat_const, Matrix.diagonal_transpose, pmOneMat_zero, mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_eq_diagonal_iff] at hcol
    have h0 := hcol (Sum.inr 0)
    nlinarith
  rw [← Matrix.smul_one_eq_diagonal] at hmat_const
  rcases sq_eq_one_iff.mp hesq with h | h
  · left
    apply mat_injective_zero
    rw [hmat_const, h, one_smul, mat_one_zero]
  · right
    apply mat_injective_zero
    rw [hmat_const, h, neg_smul, one_smul, mat_neg, mat_one_zero]

/-- Since `O(0,1) = {±1}` is abelian, its centre is everything; and `1` and `-1` are central.
This is the dimension-`0` case of `Work.Mostow.poCenter`. -/
lemma poCenter_zero : ∀ A : O1 0, A ∈ Subgroup.center (O1 0) ↔ A = 1 ∨ A = -1 := by
  intro A
  refine ⟨fun _ => O1_zero_eq_one_or_neg_one A, ?_⟩
  intro h
  rw [Subgroup.mem_center_iff]
  intro g
  rcases h with rfl | rfl
  · simp
  · apply mat_injective_zero
    simp [mat_neg]

/-! ### The triviality of the action in dimension `0` -/

/-- The chart `E 0` is a subsingleton, so its unit sphere `Sph 0` is empty. -/
lemma not_mem_Sph_zero (ξ : E 0) : ξ ∉ Sph 0 := by
  have h : ξ = 0 := Subsingleton.elim _ _
  rw [h]
  simp [Sph]

/-! ### Area T1 in dimension `0` -/

theorem poAction_zero : POActionProp 0 := by
  have hsmul : ∀ (A : O1 0) (u : E 0), (A : PO 0 1) • u = actO A u :=
    fun _ _ => Subsingleton.elim _ _
  have hfaith : ∀ g : PO 0 1, (∀ u : E 0, g • u = u) → g = 1 := by
    intro g _
    have hc : rep g ∈ Subgroup.center (O1 0) :=
      (poCenter_zero (rep g)).2 (O1_zero_eq_one_or_neg_one (rep g))
    rw [← QuotientGroup.out_eq' g]
    exact (QuotientGroup.eq_one_iff (rep g)).2 hc
  refine ⟨poCenter_zero, hsmul, ?_, ?_, ?_, hfaith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A ξ _
    exact Subsingleton.elim _ _
  · intro u
    exact Subsingleton.elim _ _
  · intro g h u
    exact Subsingleton.elim _ _
  · exact poContDescent 0 (poActCont 0).1 hsmul
  · intro g ξ hξ
    exact absurd hξ (not_mem_Sph_zero ξ)
  · intro ξ hξ
    exact absurd hξ (not_mem_Sph_zero ξ)
  · intro g h ξ hξ
    exact absurd hξ (not_mem_Sph_zero ξ)
  · intro g
    exact (poBdReg_PO 0).1 g
  · intro g
    exact (poBdReg_PO 0).2 g

/-! ### The target -/

theorem poAction_hypIso_zero :
    Submission.Mostow.POActionProp 0 ∧ Submission.Mostow.HypIsometryProp 0 :=
  ⟨poAction_zero, hypIsometryAll 0 poAction_zero⟩

end

end Work.Mostow
