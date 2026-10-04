import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset

/-- Contracting the Kulkarni–Nomizu product `A ∧ id` twice gives
`ric (A ∧ id) = (tr A) · id + (n - 2) · A`. -/
theorem ric_knProd_id2 (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)) i j =
      (∑ k, A k k) * (if i = j then (1 : ℝ) else 0) + ((n : ℝ) - 2) * A i j := by
  -- Termwise expansion of `knProd A (id2 n) k i k j`.
  have hterm : ∀ k : Fin n, knProd A (id2 n) k i k j =
      A k k * (if i = j then (1 : ℝ) else 0) - A k j * (if i = k then (1 : ℝ) else 0)
        - A i k * (if k = j then (1 : ℝ) else 0) + A i j := by
    intro k
    simp only [knProd, id2]
    split_ifs <;> ring
  -- The four contracted pieces.
  have h1 : (∑ k : Fin n, A k k * (if i = j then (1 : ℝ) else 0)) =
      (∑ k : Fin n, A k k) * (if i = j then (1 : ℝ) else 0) :=
    (Finset.sum_mul Finset.univ (fun k => A k k) (if i = j then (1 : ℝ) else 0)).symm
  have h2 : (∑ k : Fin n, A k j * (if i = k then (1 : ℝ) else 0)) = A i j := by
    rw [show (∑ k : Fin n, A k j * (if i = k then (1 : ℝ) else 0)) =
        ∑ k : Fin n, (if k = i then A k j else 0) from by
      apply Finset.sum_congr rfl; intro k _
      by_cases h : k = i
      · subst h; simp
      · simp [h, Ne.symm h]]
    simp [Finset.sum_ite_eq']
  have h3 : (∑ k : Fin n, A i k * (if k = j then (1 : ℝ) else 0)) = A i j := by
    rw [show (∑ k : Fin n, A i k * (if k = j then (1 : ℝ) else 0)) =
        ∑ k : Fin n, (if k = j then A i k else 0) from by
      apply Finset.sum_congr rfl; intro k _
      by_cases h : k = j
      · subst h; simp
      · simp [h]]
    simp [Finset.sum_ite_eq']
  have h4 : (∑ k : Fin n, A i j) = (n : ℝ) * A i j := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [ric, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
  ring

end Work.Diff.Alg.Pinch
