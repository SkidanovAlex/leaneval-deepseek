import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quadratic form of the Ricci tensor of `Q(R)`

`Work.Diff.Alg.Pinch.ric_Q` gives the `(0,2)`-tensor identity

`ric (Q R) i j = 2 ∑_{p,q} ric R p q · R i p j q`

for an algebraic curvature tensor `R`.  Contracting both slots with a vector `v` turns this into

`∑_{i,j} ric (Q R) i j vᵢ vⱼ = 2 ∑_{p,q} ric R p q · (∑_{i,j} vᵢ vⱼ R i p j q)`,

i.e. `qform (ric (Q R)) v = 2 ∑_{p,q} ric R p q · bmat v R p q`, which is the statement proved here.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- A quadruple sum is invariant under the block permutation `(i,j,p,q) ↦ (p,q,i,j)`. -/
private lemma sum4_reindex (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q, f i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
  calc ∑ i, ∑ j, ∑ p, ∑ q, f i j p q
      = ∑ i, ∑ p, ∑ j, ∑ q, f i j p q := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
    _ = ∑ p, ∑ i, ∑ j, ∑ q, f i j p q := by rw [Finset.sum_comm]
    _ = ∑ p, ∑ i, ∑ q, ∑ j, f i j p q := by
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_comm]

/-- Pushing a scalar factor through a double sum on the right. -/
private lemma sum2_mul (f : Fin n → Fin n → ℝ) (c : ℝ) :
    (∑ p, ∑ q, f p q) * c = ∑ p, ∑ q, f p q * c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_mul]

/-- Pulling a scalar factor out of a double sum on the left. -/
private lemma mul_sum2 (c : ℝ) (f : Fin n → Fin n → ℝ) :
    c * (∑ i, ∑ j, f i j) = ∑ i, ∑ j, c * f i j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

theorem qform_ric_Q (n : ℕ) {E : Submission.Diff.Alg.Curv4 n} (hE : Submission.Diff.Alg.IsAlgCurv E)
    (v : Fin n → ℝ) :
    Work.Diff.Alg.Pinch.qform (Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.Q E)) v
      = 2 * ∑ p, ∑ q, Work.Diff.Alg.Pinch.ric E p q * Work.Diff.Alg.Pinch.bmat v E p q := by
  have hric : ∀ i j : Fin n,
      ric (Q E) i j = 2 * ∑ p, ∑ q, ric E p q * E i p j q := ric_Q n hE
  have hstep1 : (∑ i, ∑ j, ric (Q E) i j * v i * v j)
      = 2 * ∑ i, ∑ j, (∑ p, ∑ q, ric E p q * E i p j q) * v i * v j := by
    rw [show (∑ i, ∑ j, ric (Q E) i j * v i * v j)
        = ∑ i, ∑ j, (2 * ∑ p, ∑ q, ric E p q * E i p j q) * v i * v j from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hric i j]))]
    rw [show (∑ i, ∑ j, (2 * ∑ p, ∑ q, ric E p q * E i p j q) * v i * v j)
        = ∑ i, ∑ j, 2 * ((∑ p, ∑ q, ric E p q * E i p j q) * v i * v j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  have hstep2 : (∑ i, ∑ j, (∑ p, ∑ q, ric E p q * E i p j q) * v i * v j)
      = ∑ i, ∑ j, ∑ p, ∑ q, (ric E p q * E i p j q) * v i * v j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [sum2_mul (fun p q => ric E p q * E i p j q) (v i)]
    rw [sum2_mul (fun p q => (ric E p q * E i p j q) * v i) (v j)]
  have hstep3 : (∑ i, ∑ j, ∑ p, ∑ q, (ric E p q * E i p j q) * v i * v j)
      = ∑ p, ∑ q, ∑ i, ∑ j, (ric E p q * E i p j q) * v i * v j :=
    sum4_reindex (fun i j p q => (ric E p q * E i p j q) * v i * v j)
  have hstep4 : (∑ p, ∑ q, ∑ i, ∑ j, (ric E p q * E i p j q) * v i * v j)
      = ∑ p, ∑ q, ∑ i, ∑ j, ric E p q * (v i * v j * E i p j q) := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hstep5 : (∑ p, ∑ q, ∑ i, ∑ j, ric E p q * (v i * v j * E i p j q))
      = ∑ p, ∑ q, ric E p q * (∑ i, ∑ j, v i * v j * E i p j q) := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [mul_sum2 (ric E p q) (fun i j => v i * v j * E i p j q)]
  have key : (∑ i, ∑ j, ric (Q E) i j * v i * v j)
      = 2 * ∑ p, ∑ q, ric E p q * (∑ i, ∑ j, v i * v j * E i p j q) := by
    rw [hstep1, hstep2, hstep3, hstep4, hstep5]
  simp only [qform, bmat]
  rw [key]

end Work.Diff.Alg.Pinch
