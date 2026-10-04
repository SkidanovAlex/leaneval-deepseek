import Mathlib
import Submission.Work.Diff.GE.frobSq5_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open Finset LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg

/-!
# `frobSq5` as a sum over the index functions `Fin 5 → Fin n`

`frobSq5 S = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, S m i j k l ^ 2` is a five-fold nested sum, while the
intended re-indexed form is a sum over `x : Fin 5 → Fin n` of `S (x 0) (x 1) (x 2) (x 3) (x 4) ^ 2`.

The two are related by the evaluation equivalence
`piFiveEquiv n : (Fin 5 → Fin n) ≃ Fin n × (Fin n × (Fin n × (Fin n × Fin n)))`,
`Fintype.sum_equiv`, and the elementary peeling `sum_prod5` of a sum over a nested product.
-/

/-- The evaluation equivalence `(Fin 5 → Fin n) ≃ Fin n × (Fin n × (Fin n × (Fin n × Fin n)))`;
the inverse rebuilds the function by the nested `Fin.cases` chain. -/
def piFiveEquiv (n : ℕ) :
    (Fin 5 → Fin n) ≃ (Fin n × (Fin n × (Fin n × (Fin n × Fin n)))) where
  toFun f := (f 0, f 1, f 2, f 3, f 4)
  invFun p := fun i =>
    Fin.cases p.1
      (fun j => Fin.cases p.2.1
        (fun k => Fin.cases p.2.2.1
          (fun l => Fin.cases p.2.2.2.1 (fun _ => p.2.2.2.2) l) k) j) i
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d, e⟩ := p
    rfl

/-- A sum over a four-fold nested product as five nested sums. -/
lemma sum_prod5 {n : ℕ} (g : Fin n × (Fin n × (Fin n × (Fin n × Fin n))) → ℝ) :
    (∑ p, g p) = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
      g (a, b, c, d, e) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fintype.sum_prod_type]

theorem frobSq5_eq_sum {n : ℕ} (T : Fin n → Curv4 n) : frobSq5 T = ∑ x : Fin 5 → Fin n, (T (x 0) (x 1) (x 2) (x 3) (x 4)) ^ 2 := by
  rw [frobSq5]
  rw [Fintype.sum_equiv (piFiveEquiv n)
      (fun x : Fin 5 → Fin n => (T (x 0) (x 1) (x 2) (x 3) (x 4)) ^ 2)
      (fun p : Fin n × (Fin n × (Fin n × (Fin n × Fin n))) =>
        (T p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ^ 2)
      (fun x => rfl)]
  exact (sum_prod5 (fun p => (T p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ^ 2)).symm

end Work.Diff.GE
