import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The index identity `E1 = S1`

`Work.Diff.Alg.Pinch.Q2Defs` expands the two sides of

`Phi (Q2 R) X (bar X) = (Tmat R X * Rm R).trace`

into explicit sums `S1, S2` (left-hand side) and `E1, E2, E3, E4` (right-hand side).
The present file proves the first of the four matching identities: for an algebraic
curvature tensor `R` (`Submission.Diff.Alg.IsAlgCurv`) one has `E1 R X = S1 R X`.

In components (`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`),

* `E1 R X = ∑ i j k l a c, R i j k l · R c l a j · conj (X (i,a)) · X (k,c)`;
* `S1 R X = ∑ i j k l p q, R i p k q · R j p l q · X (i,j) · conj (X (k,l))`.

The proof is pure index manipulation: relabel the six summation indices of `S1`
by the involution `(i,j,k,l,p,q) ↦ (k,c,i,a,l,j)` and then use the pair symmetry
`R k l i j = R i j k l` of an algebraic curvature tensor together with commutativity
of the product in `ℂ`.  Both `E1` and `S1` are first flattened to sums over three
pairs of indices (`Fintype.sum_prod_type`) and the relabelling is realised as an
involution of the index set, handled by `Equiv.sum_comp`.

The companion identities `E2 = S2`, `E3 = S2`, `E4 = S1` are of exactly the same
shape.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- `E1` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(a,c)` of indices. -/
private def eFlat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) → ℂ :=
  fun x => (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ) * (R x.2.2.2 x.2.1.2 x.2.2.1 x.1.2 : ℂ)
    * bar X (x.1.1, x.2.2.1) * X (x.2.1.1, x.2.2.2)

/-- `S1` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(p,q)` of indices. -/
private def sFlat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) → ℂ :=
  fun x => (R x.1.1 x.2.2.1 x.2.1.1 x.2.2.2 : ℂ) * (R x.1.2 x.2.2.1 x.2.1.2 x.2.2.2 : ℂ)
    * X (x.1.1, x.1.2) * bar X (x.2.1.1, x.2.1.2)

/-- The involution of triples of pairs realising the relabelling
`(i,j,k,l,p,q) ↦ (k,c,i,a,l,j)` on the six indices.  With `x = (p, (q, r))` it sends
`(p,q,r)` to `((q.1,r.2), (p.1,r.1), (q.2,p.2))`. -/
private def sig {n : ℕ} : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) →
                       (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) :=
  fun x => (⟨x.2.1.1, x.2.2.2⟩, (⟨x.1.1, x.2.2.1⟩, ⟨x.2.1.2, x.1.2⟩))

/-- `sig` packaged as an equivalence (it is an involution). -/
private def sigEquiv {n : ℕ} : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) ≃
                       (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) :=
  ⟨sig, sig, by rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩; rfl, by rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩; rfl⟩

/-- The pointwise identity `eFlat = sFlat ∘ sig`, using the pair symmetry of `R`. -/
private lemma eFlat_eq {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ)
    (x : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)) :
    eFlat R X x = sFlat R X (sig x) := by
  simp only [eFlat, sFlat, sig]
  rw [hR.2.1 x.1.1 x.1.2 x.2.1.1 x.2.1.2]
  ring

/-- `E1` as a sum over three pairs of indices. -/
private lemma E1_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    E1 R X = ∑ x, eFlat R X x := by
  simp only [E1, eFlat, Fintype.sum_prod_type]

/-- `S1` as a sum over three pairs of indices. -/
private lemma S1_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    S1 R X = ∑ x, sFlat R X x := by
  simp only [S1, sFlat, Fintype.sum_prod_type]

theorem E1_eq_S1 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.E1 R X = Work.Diff.Alg.Pinch.S1 R X := by
  rw [E1_flat, S1_flat]
  rw [← Equiv.sum_comp (sigEquiv (n := n)) (sFlat R X)]
  apply Finset.sum_congr rfl
  intro x _
  exact eFlat_eq R hR X x

end Work.Diff.Alg.Pinch
