import Mathlib
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
/-- `|Ric|² ≤ n |Rm|²` for the components in an orthonormal frame, `Ricᵢⱼ = ∑ₖ Rₖᵢₖⱼ`.

For fixed `i, j` Cauchy–Schwarz in the trace index `k` gives
`(∑ₖ Rₖᵢₖⱼ)² ≤ n ∑ₖ Rₖᵢₖⱼ²`, and the latter sum of `n³` squares is a sub-sum of the `n⁴`
squares of `frobSq`.  (No symmetry of `R` is used.) -/
theorem ricSq_le_frobSq {n : ℕ} (R : Curv4 n) : ricSq R ≤ (n : ℝ) * frobSq R := by
  -- Cauchy–Schwarz in the trace index.
  have hcs : ∀ i j : Fin n, (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * ∑ k, (R k i k j) ^ 2 := by
    intro i j
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin n => R k i k j)
    simpa using h
  -- `∑ i j a c (R a i c j)² = frobSq R` (a permutation of the four summation indices).
  have hab : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ c : Fin n, (R a i c j) ^ 2)
      = frobSq R := by
    have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ c : Fin n, (R a i c j) ^ 2)
        = (∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ c : Fin n, (R a i c j) ^ 2) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact Finset.sum_comm
    have h2 : (∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ c : Fin n, (R a i c j) ^ 2)
        = (∑ i : Fin n, ∑ a : Fin n, ∑ c : Fin n, ∑ j : Fin n, (R a i c j) ^ 2) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact Finset.sum_comm
    have h3 : (∑ i : Fin n, ∑ a : Fin n, ∑ c : Fin n, ∑ j : Fin n, (R a i c j) ^ 2)
        = (∑ a : Fin n, ∑ i : Fin n, ∑ c : Fin n, ∑ j : Fin n, (R a i c j) ^ 2) :=
      Finset.sum_comm
    rw [h1, h2, h3]
    rfl
  -- the restricted sum of squares is bounded by the full Frobenius sum.
  have hsub : ∀ i j : Fin n, (∑ k, (R k i k j) ^ 2) ≤ ∑ a, ∑ c, (R a i c j) ^ 2 := by
    intro i j
    calc (∑ k : Fin n, (R k i k j) ^ 2)
        = ∑ a : Fin n, (R a i a j) ^ 2 := rfl
      _ ≤ ∑ a : Fin n, ∑ c : Fin n, (R a i c j) ^ 2 := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          exact Finset.single_le_sum (s := Finset.univ) (f := fun c : Fin n => (R a i c j) ^ 2)
            (fun c _ => sq_nonneg _) (Finset.mem_univ a)
  have hsumsub : (∑ i, ∑ j, ∑ k, (R k i k j) ^ 2)
      ≤ ∑ i, ∑ j, ∑ a, ∑ c, (R a i c j) ^ 2 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsub i j))
  have hA : (∑ i, ∑ j, ∑ k, (R k i k j) ^ 2) ≤ frobSq R :=
    le_trans hsumsub (le_of_eq hab)
  have hmid : ricSq R ≤ (n : ℝ) * (∑ i, ∑ j, ∑ k, (R k i k j) ^ 2) := by
    simp only [ricSq]
    calc ∑ i, ∑ j, (∑ k, R k i k j) ^ 2
        ≤ ∑ i, ∑ j, (n : ℝ) * ∑ k, (R k i k j) ^ 2 :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcs i j))
      _ = (n : ℝ) * ∑ i, ∑ j, ∑ k, (R k i k j) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  exact le_trans hmid (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg n))

end Work.Diff.GE.Gest
