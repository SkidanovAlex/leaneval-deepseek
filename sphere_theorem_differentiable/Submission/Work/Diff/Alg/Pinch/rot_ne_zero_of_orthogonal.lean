import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.rot_contract4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `rot A` is injective for `A ∈ O(n)`

The orthogonal group acts on `4`-index curvature arrays by
`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`
(`Submission.Diff.Alg.rot`).  Since `A` is invertible with inverse `Aᵀ`, this action is faithful:
`rot A R = 0` forces `R = 0`.

The proof uses the complete contraction identity `Work.Diff.Alg.rot_contract4`: contracting
`rot A R` against the four rotated basis vectors gives back the four-index contraction of `R`.
With `α = e_p, β = e_q, γ = e_r, δ = e_s` (so that the right-hand side is the single component
`R p q r s`) the identity reads

`rot Aᵀ (rot A R) p q r s = R p q r s`,

because `A e_p` is the `p`-th column of `A`, i.e. the `p`-th row of `Aᵀ`.  Hence `rot A R = 0`
implies `R = 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open scoped Matrix

variable {n : ℕ}

/-- A single component of `R` as a four-fold contraction against the standard basis vectors. -/
lemma sum4_basis_mul (R : Curv4 n) (p q r s : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d,
        (Pi.single p (1 : ℝ) : Fin n → ℝ) a * (Pi.single q (1 : ℝ) : Fin n → ℝ) b
          * (Pi.single r (1 : ℝ) : Fin n → ℝ) c * (Pi.single s (1 : ℝ) : Fin n → ℝ) d
          * R a b c d) = R p q r s := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single s]
        · simp
        · intro m _ hm; simp [Pi.single_eq_of_ne hm]
        · intro h; exact absurd (Finset.mem_univ s) h
      · intro m _ hm; simp [Pi.single_eq_of_ne hm]
      · intro h; exact absurd (Finset.mem_univ r) h
    · intro m _ hm; simp [Pi.single_eq_of_ne hm]
    · intro h; exact absurd (Finset.mem_univ q) h
  · intro m _ hm; simp [Pi.single_eq_of_ne hm]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- The left-hand side of `Work.Diff.Alg.rot_contract4` at the standard basis vectors is `rot Aᵀ`
of the tensor at the same indices: `A e_p` is the `p`-th column of `A`. -/
lemma sum4_mulVec_basis (A : Matrix (Fin n) (Fin n) ℝ) (S : Curv4 n) (p q r s : Fin n) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        Matrix.mulVec A (Pi.single p (1 : ℝ)) i * Matrix.mulVec A (Pi.single q 1) j
          * Matrix.mulVec A (Pi.single r 1) k * Matrix.mulVec A (Pi.single s 1) l
          * S i j k l)
      = rot Aᵀ S p q r s := by
  have hp : ∀ i, Matrix.mulVec A (Pi.single p (1 : ℝ)) i = A i p := by
    intro i; rw [Matrix.mulVec_single]; simp [Matrix.col_apply]
  have hq : ∀ j, Matrix.mulVec A (Pi.single q (1 : ℝ)) j = A j q := by
    intro j; rw [Matrix.mulVec_single]; simp [Matrix.col_apply]
  have hr : ∀ k, Matrix.mulVec A (Pi.single r (1 : ℝ)) k = A k r := by
    intro k; rw [Matrix.mulVec_single]; simp [Matrix.col_apply]
  have hs : ∀ l, Matrix.mulVec A (Pi.single s (1 : ℝ)) l = A l s := by
    intro l; rw [Matrix.mulVec_single]; simp [Matrix.col_apply]
  simp only [hp, hq, hr, hs, rot, Matrix.transpose_apply]

theorem rot_ne_zero_of_orthogonal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : R ≠ 0) : Submission.Diff.Alg.rot A R ≠ 0 := by
  intro h
  apply hR
  funext p q r s
  have hc := rot_contract4 A hA R (Pi.single p (1 : ℝ)) (Pi.single q 1)
    (Pi.single r 1) (Pi.single s 1)
  rw [sum4_mulVec_basis A (rot A R) p q r s] at hc
  rw [sum4_basis_mul R p q r s] at hc
  rw [h] at hc
  simp only [rot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hc
  exact hc.symm

end Work.Diff.Alg.Pinch
