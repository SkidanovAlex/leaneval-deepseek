import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

/-- For `i : Fin N`, the product over the predecessors of `i` (in the linear order on `Fin N`)
may be rewritten as a product over `Finset.range i.1` after mapping `j ↦ j.1`. -/
private lemma prod_Iio_val (M : Type*) [CommMonoid M] (N : ℕ) (i : Fin N) (f : ℕ → M) :
    (∏ j ∈ Finset.Iio i, f j.1) = ∏ n ∈ Finset.range i.1, f n := by
  refine Finset.prod_bij (fun j _ => j.1) ?_ ?_ ?_ ?_
  · intro j hj
    have h : (j : ℕ) < (i : ℕ) := (Finset.mem_Iio (a := i) (x := j)).mp hj
    exact Finset.mem_range.mpr h
  · intro a _ b _ h
    exact Fin.val_injective h
  · intro n hn
    have hn' : n < (i : ℕ) := Finset.mem_range.mp hn
    have hn'' : n < N := lt_of_lt_of_le hn' (Nat.le_of_lt i.isLt)
    refine ⟨⟨n, hn''⟩, ?_, rfl⟩
    exact (Finset.mem_Iio (a := i) (x := ⟨n, hn''⟩)).mpr hn'
  · intro j _
    rfl

/-- The product over all ordered pairs `j < i` of `‖x j - x i‖` may be computed either by
iterating over `i : Fin N` (with `j` ranging over `Finset.Iio i`) or by iterating over
`i ∈ Finset.range N` (with `j` ranging over `Finset.range i`). -/
theorem prod_Iio_eq_prod_range (x : ℕ → ℂ) (N : ℕ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Iio i, ‖x j.1 - x i.1‖)
      = ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range i, ‖x j - x i‖ := by
  rw [← Fin.prod_univ_eq_prod_range (fun n => ∏ j ∈ Finset.range n, ‖x j - x n‖) N]
  apply Finset.prod_congr rfl
  intro i _
  exact prod_Iio_val ℝ N i (fun n => ‖x n - x i.1‖)

end Commons.Data.Fin
