import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.ric_Q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quadratic form of `ric (Q R)`

`Work.Diff.Alg.Pinch.ric_Q` computes the Ricci tensor of Hamilton's reaction term:
`ric (Q R) i j = 2 ∑_{p,q} ric R p q · R i p j q`.  Contracting that identity with a vector `v`
and collecting the sums gives

`∑_{i,j} ric (Q R) i j vᵢ vⱼ = 2 ∑_{p,q} ric R p q · (∑_{i,j} R i p j q vᵢ vⱼ)`,

which is the `(0,2)`-tensor form of the identity (`Ric(Q R) = 2 Ric(R) ⌟ R`), the shape in which it
is used for the Böhm–Wilking pinching-set argument.  The content beyond `ric_Q` is purely the
exchange of the two blocks `(i,j)` and `(p,q)` of a quadruple sum.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- A quadruple sum is unchanged by exchanging the two blocks `(i,j)` and `(p,q)` of summation
variables. -/
private lemma sum4_block (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, F i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, F i j p q := by
  calc (∑ i, ∑ j, ∑ p, ∑ q, F i j p q)
      = ∑ i, ∑ p, ∑ j, ∑ q, F i j p q := by
        apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, F i j p q := Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ q, ∑ j, F i j p q := by
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ i, ∑ j, F i j p q := by
        apply Finset.sum_congr rfl; intro p _
        exact Finset.sum_comm

/-- Pulling the factor `2` out of the two outer sums. -/
private lemma two_mul_qform (S : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (2 * S i j) * v i * v j) = 2 * (∑ i, ∑ j, S i j * v i * v j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The core reordering: contracting the `(0,2)`-tensor `∑_{p,q} (ric R p q) · R i p j q` with `v`
equals `2`-free version of the claimed identity. -/
private lemma qform_ric_contract (R : Curv4 n) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (∑ p, ∑ q, ric R p q * R i p j q) * v i * v j)
      = ∑ p, ∑ q, ric R p q * (∑ i, ∑ j, R i p j q * v i * v j) := by
  have hL : (∑ i, ∑ j, (∑ p, ∑ q, ric R p q * R i p j q) * v i * v j)
      = ∑ i, ∑ j, ∑ p, ∑ q, (ric R p q * R i p j q) * (v i * v j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [show (∑ p, ∑ q, ric R p q * R i p j q) * v i
        = ∑ p, ∑ q, (ric R p q * R i p j q) * v i from by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_mul]]
    rw [show (∑ p, ∑ q, (ric R p q * R i p j q) * v i) * v j
        = ∑ p, ∑ q, ((ric R p q * R i p j q) * v i) * v j from by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_mul]]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  have hR' : (∑ p, ∑ q, ric R p q * (∑ i, ∑ j, R i p j q * v i * v j))
      = ∑ p, ∑ q, ∑ i, ∑ j, ric R p q * (R i p j q * v i * v j) := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  rw [hL, sum4_block]
  rw [hR']
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem ricForm_Q (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) (v : Fin n → ℝ) :
    (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.Q R) i j * v i * v j)
      = 2 * ∑ p, ∑ q, Work.Diff.Alg.Pinch.ric R p q
          * (∑ i, ∑ j, R i p j q * v i * v j) := by
  have hsub : (∑ i, ∑ j, ric (Q R) i j * v i * v j)
      = ∑ i, ∑ j, (2 * (∑ p, ∑ q, ric R p q * R i p j q)) * v i * v j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ric_Q n hR i j]
  rw [hsub, two_mul_qform, qform_ric_contract]

end Work.Diff.Alg.Pinch
