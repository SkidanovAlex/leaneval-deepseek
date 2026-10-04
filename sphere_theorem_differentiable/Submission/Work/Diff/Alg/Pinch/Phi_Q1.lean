import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "operator square" part `Q₁` of Hamilton's reaction term, in the operator picture

`Q₁(R)ᵢⱼₖₗ = ∑ₚq Rᵢⱼₚq Rₖₗₚq` is, as a matrix on the space of pair-indexed vectors, the square of
`Rm R` (the symmetry `Rₖₗᵢⱼ = Rᵢⱼₖₗ` of an algebraic curvature tensor is exactly what makes the
square equal to its transpose-product).  Consequently the associated bilinear form `Phi (Q1 R)`
factorises as the (Euclidean) pairing of the two vectors `Rop R X` and `Rop R Y`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- Sum-factorisation for a *symmetric* kernel: `∑ₚ ∑_q (∑_r A p r * A q r) X_p Y_q`
equals `∑_p (∑_r A p r * X_r)(∑_r A p r * Y_r)`.  (The symmetry of `A` turns the matrix
`A Aᵀ` into `A²`.) -/
lemma symm_sum {α : Type*} [Fintype α]
    (A : α → α → ℂ) (hA : ∀ p q, A p q = A q p) (X Y : α → ℂ) :
    (∑ p, ∑ q, (∑ r, A p r * A q r) * X p * Y q)
      = ∑ p, (∑ r, A p r * X r) * (∑ r, A p r * Y r) := by
  have e1 : ∀ p q, (∑ r, A p r * A q r) * X p * Y q
      = ∑ r, A p r * A q r * X p * Y q := by
    intro p q
    rw [Finset.sum_mul, Finset.sum_mul]
  simp only [e1]
  have step1 : (∑ p, ∑ q, ∑ r, A p r * A q r * X p * Y q)
      = ∑ p, ∑ r, ∑ q, A p r * A q r * X p * Y q := by
    apply Finset.sum_congr rfl; intro p _
    exact Finset.sum_comm
  have step2 : (∑ p, ∑ r, ∑ q, A p r * A q r * X p * Y q)
      = ∑ r, ∑ p, ∑ q, A p r * A q r * X p * Y q := Finset.sum_comm
  rw [step1, step2]
  have step3 : (∑ r, ∑ p, ∑ q, A p r * A q r * X p * Y q)
      = ∑ r, (∑ p, A p r * X p) * (∑ q, A q r * Y q) := by
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  rw [step3]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  · exact Finset.sum_congr rfl (fun p _ => by rw [hA p r])
  · exact Finset.sum_congr rfl (fun q _ => by rw [hA q r])

/-- `Q₁` as a pair-indexed sum: the cast to `ℂ` of `Q₁(R)ᵢⱼₖₗ` is the sum over the pair index
`r : Fin n × Fin n` of the two `Rm`-entries. -/
lemma Q1_cast (n : ℕ) (R : Curv4 n) (P Q : Fin n × Fin n) :
    (Q1 R P.1 P.2 Q.1 Q.2 : ℂ)
      = ∑ r : Fin n × Fin n, (R P.1 P.2 r.1 r.2 : ℂ) * (R Q.1 Q.2 r.1 r.2 : ℂ) := by
  simp only [Q1]
  push_cast
  rw [Fintype.sum_prod_type]

theorem Phi_Q1 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X Y : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.Phi (Work.Diff.Alg.Pinch.Q1 R) X Y
      = ∑ p : Fin n × Fin n, Work.Diff.Alg.Pinch.Rop R X p * Work.Diff.Alg.Pinch.Rop R Y p := by
  have key : (∑ (p : Fin n × Fin n), ∑ (q : Fin n × Fin n),
        (∑ (r : Fin n × Fin n), (R p.1 p.2 r.1 r.2 : ℂ) * (R q.1 q.2 r.1 r.2 : ℂ)) * X p * Y q)
      = ∑ (p : Fin n × Fin n), (∑ (r : Fin n × Fin n), (R p.1 p.2 r.1 r.2 : ℂ) * X r)
          * (∑ (r : Fin n × Fin n), (R p.1 p.2 r.1 r.2 : ℂ) * Y r) :=
    symm_sum (fun p q : Fin n × Fin n => (R p.1 p.2 q.1 q.2 : ℂ))
      (fun p q => by simp only [hR.2.1 q.1 q.2 p.1 p.2]) X Y
  rw [show Phi (Q1 R) X Y
        = ∑ (p : Fin n × Fin n), ∑ (q : Fin n × Fin n),
            (∑ (r : Fin n × Fin n), (R p.1 p.2 r.1 r.2 : ℂ) * (R q.1 q.2 r.1 r.2 : ℂ)) * X p * Y q
        from by simp only [Phi, Q1_cast], key]
  rfl

end Work.Diff.Alg.Pinch
