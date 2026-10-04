import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The index identity `E4 = S1`

`Work.Diff.Alg.Pinch.Q2Defs` expands the two sides of

`Phi (Q2 R) X (bar X) = (Tmat R X * Rm R).trace`

into explicit sums `S1, S2` (left-hand side) and `E1, E2, E3, E4` (right-hand side).
The present file proves the fourth of the four matching identities: for an algebraic
curvature tensor `R` (`Submission.Diff.Alg.IsAlgCurv`) one has `E4 R X = S1 R X`.

In components (`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`),

* `E4 R X = ∑ i j k l b d, R i j k l · R k d i b · conj (X (b,j)) · X (d,l)`;
* `S1 R X = ∑ i j k l p q, R i p k q · R j p l q · X (i,j) · conj (X (k,l))`.

The proof is pure index manipulation.  Relabel the six summation indices of `E4` by
`(i,j,k,l,b,d) ↦ (i',j',k',l',p',q') = (d,l,b,j,k,i)`; then, term by term,

`R i j k l = R l k j i` and `R k d i b = R d k b i`

(the two index symmetries `R a b c d = R b a d c` — exchanging the two indices of each
pair — together with the pair symmetry `R k l i j = R i j k l`), while the two factors
`X (d,l) · conj (X (b,j))` reorder to `X (i',j') · conj (X (k',l'))`.  After the
relabelling `E4` is literally `S1`.

Both `E4` and `S1` are first flattened to sums over three pairs of indices
(`Fintype.sum_prod_type`), and the relabelling is realised as an involution of the
index set, handled by `Equiv.sum_comp`, exactly as in `E1_eq_S1`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- Exchanging the two indices inside each pair: `R a b c d = R b a d c` for an algebraic
curvature tensor.  This is two applications of antisymmetry in the first pair, combined with
pair symmetry (equivalently, antisymmetry in both pairs). -/
private lemma swap_both {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n) :
    R a b c d = R b a d c := by
  linarith [hR.2.1 a b c d, hR.1 c d a b, hR.2.1 d c a b, hR.1 a b d c]

/-- `E4` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(b,d)` of indices. -/
private def eFlat4 {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) → ℂ :=
  fun x => (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ) * (R x.2.1.1 x.2.2.2 x.1.1 x.2.2.1 : ℂ)
    * bar X (x.2.2.1, x.1.2) * X (x.2.2.2, x.2.1.2)

/-- `S1` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(p,q)` of indices. -/
private def sFlat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) → ℂ :=
  fun x => (R x.1.1 x.2.2.1 x.2.1.1 x.2.2.2 : ℂ) * (R x.1.2 x.2.2.1 x.2.1.2 x.2.2.2 : ℂ)
    * X (x.1.1, x.1.2) * bar X (x.2.1.1, x.2.1.2)

/-- The involution of triples of pairs realising the relabelling
`(i,j,k,l,b,d) ↦ (d,l,b,j,k,i)` on the six indices.  With `x = (p, (q, r))` it sends
`(p,q,r)` to `((r.2,q.2), (r.1,p.2), (q.1,p.1))`. -/
private def sig4 {n : ℕ} : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) →
                        (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) :=
  fun x => (⟨x.2.2.2, x.2.1.2⟩, (⟨x.2.2.1, x.1.2⟩, ⟨x.2.1.1, x.1.1⟩))

/-- `sig4` packaged as an equivalence (it is an involution). -/
private def sigEquiv4 {n : ℕ} : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) ≃
                        (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) :=
  ⟨sig4, sig4, by rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩; rfl, by rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩; rfl⟩

/-- The pointwise identity `eFlat4 = sFlat ∘ sig4`, using the index symmetries of `R`. -/
private lemma eFlat4_eq {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ)
    (x : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)) :
    eFlat4 R X x = sFlat R X (sig4 x) := by
  have h1 : R x.2.1.2 x.2.1.1 x.1.2 x.1.1 = R x.1.1 x.1.2 x.2.1.1 x.2.1.2 := by
    rw [hR.2.1 x.1.2 x.1.1 x.2.1.2 x.2.1.1, swap_both R hR x.1.2 x.1.1 x.2.1.2 x.2.1.1]
  have h2 : R x.2.1.1 x.2.2.2 x.1.1 x.2.2.1 = R x.2.2.2 x.2.1.1 x.2.2.1 x.1.1 :=
    swap_both R hR x.2.1.1 x.2.2.2 x.1.1 x.2.2.1
  simp only [eFlat4, sFlat, sig4, h1, h2]
  ring

/-- `E4` as a sum over three pairs of indices. -/
private lemma E4_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    E4 R X = ∑ x, eFlat4 R X x := by
  simp only [E4, eFlat4, Fintype.sum_prod_type]

/-- `S1` as a sum over three pairs of indices. -/
private lemma S1_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    S1 R X = ∑ x, sFlat R X x := by
  simp only [S1, sFlat, Fintype.sum_prod_type]

theorem E4_eq_S1 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.E4 R X = Work.Diff.Alg.Pinch.S1 R X := by
  rw [E4_flat, S1_flat]
  rw [← Equiv.sum_comp (sigEquiv4 (n := n)) (sFlat R X)]
  apply Finset.sum_congr rfl
  intro x _
  exact eFlat4_eq R hR X x

end Work.Diff.Alg.Pinch
