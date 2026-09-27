import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poCenterDefs
import Submission.Work.Mostow.boostForm

/-!
# The centre of `O(n,1)` is `{±1}`  —  `Work.Mostow.poCenter`

`O1 n` is the unitary group of the matrix algebra `MatrixSum (Fin n) (Fin 1) ℝ` with respect to
the star operation `A ↦ J Aᵀ J`, i.e. the indefinite orthogonal group `O(n,1)`; here
`J = pmOneMat = diag(1,…,1,−1)` and `mat A` is the underlying `(n+1) × (n+1)` matrix.

Let `A` be central.  Testing `A` against the diagonal sign matrix `diagSign b` (a `−1` at the
index `b`, `1` elsewhere) shows that `mat A` has no off-diagonal entries, i.e. `mat A` is
diagonal.  Testing `A` against the hyperbolic boostMat_poCenterDefs `boostMat_poCenterDefs i (5/4) (3/4)` in the
`(e_i, e_time)`-plane, whose spatial/time entry is `3/4 ≠ 0`, shows that the `i`-th spatial
diagonal entry equals the time diagonal entry, so `mat A = e • 1` for a single scalar `e`.
Finally the defining relation `(mat A)ᵀ J (mat A) = J` of `O(n,1)` forces `e ^ 2 = 1`, so
`e = ±1` and `A = ±1`.  Conversely `±1` are of course central.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-- The hyperbolic boostMat_poCenterDefs with `cosh`-parameter `5/4` and `sinh`-parameter `3/4`, as an element
of `O(n,1)`: it mixes the spatial coordinate `i` with the time coordinate, so its
`(inl i, inr 0)`-entry is `3/4 ≠ 0`. -/
def boostElem (i : Fin n) : O1 n :=
  O1.ofMatrix (boostMat_poCenterDefs i (5 / 4) (3 / 4)) (boostForm n i (5 / 4) (3 / 4) (by norm_num))

@[simp] lemma mat_boostElem (i : Fin n) : mat (boostElem i) = boostMat_poCenterDefs i (5 / 4) (3 / 4) :=
  mat_O1_ofMatrix _ _

theorem poCenter (n : ℕ) (hn : 2 ≤ n) :
    ∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1 := by
  intro A
  constructor
  · intro hA
    rw [Subgroup.mem_center_iff] at hA
    -- (1) `A` commutes with the diagonal sign matrix with a `-1` at `b`, so all entries of
    -- `mat A` off the diagonal vanish.
    have hoff : ∀ a b : Fin n ⊕ Fin 1, a ≠ b → mat A a b = 0 := by
      intro a b hab
      have hentry : (mat (diagSignElem b) * mat A) a b = (mat A * mat (diagSignElem b)) a b := by
        have := congrArg (fun X : O1 n => mat X a b) (hA (diagSignElem b))
        simpa [mat_mul] using this
      simp only [mat_diagSignElem, diagSign, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      rw [if_neg hab] at hentry
      simp at hentry
      linarith
    -- (2) hence `mat A` is diagonal.
    have hdiag : mat A = Matrix.diagonal (fun c => mat A c c) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.diagonal_apply, if_neg hab]
        exact hoff a b hab
    -- (3) commuting with a boostMat_poCenterDefs equates the `i`-th spatial diagonal entry with the time entry.
    have hentry_eq : ∀ i : Fin n, mat A (Sum.inl i) (Sum.inl i) = mat A (Sum.inr 0) (Sum.inr 0) := by
      intro i
      have hb : (mat (boostElem i) * mat A) (Sum.inl i) (Sum.inr 0) =
                (mat A * mat (boostElem i)) (Sum.inl i) (Sum.inr 0) := by
        have := congrArg (fun X : O1 n => mat X (Sum.inl i) (Sum.inr 0)) (hA (boostElem i))
        simpa [mat_mul] using this
      rw [mat_boostElem i, hdiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hb
      simp only [boost_apply_spatial_time] at hb
      rw [mul_comm (mat A (Sum.inl i) (Sum.inl i)) ((3 : ℝ) / 4)] at hb
      exact (mul_left_cancel₀ (by norm_num : (3 : ℝ) / 4 ≠ 0) hb).symm
    -- (4) all diagonal entries of `mat A` are equal.
    have hconst : ∀ c : Fin n ⊕ Fin 1, mat A c c = mat A (Sum.inr 0) (Sum.inr 0) := by
      intro c
      rcases c with i | j
      · exact hentry_eq i
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rfl
    have hmat_const : mat A = Matrix.diagonal
        (fun _ : Fin n ⊕ Fin 1 => mat A (Sum.inr 0) (Sum.inr 0)) := by
      rw [hdiag, Matrix.diagonal_eq_diagonal_iff]
      exact hconst
    set e := mat A (Sum.inr 0) (Sum.inr 0) with he
    -- (5) the defining relation `(mat A)ᵀ J (mat A) = J` forces `e ^ 2 = 1`.
    have hesq : e ^ 2 = 1 := by
      have hcol := O1_form_col A
      rw [hmat_const, Matrix.diagonal_transpose, pmOneMat_eq_diagonal_poCenterDefs, mul_assoc,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_eq_diagonal_iff] at hcol
      have h0 := hcol (Sum.inr 0)
      simp only [jSign_inr] at h0
      nlinarith
    rw [← Matrix.smul_one_eq_diagonal] at hmat_const
    rcases sq_eq_one_iff.mp hesq with h | h
    · left
      apply mat_injective
      rw [hmat_const, h, one_smul, mat_one]
    · right
      apply mat_injective
      rw [hmat_const, h, neg_smul, one_smul, mat_neg, mat_one]
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    rcases h with rfl | rfl
    · simp
    · apply mat_injective
      simp [mat_neg]

end

end Work.Mostow
