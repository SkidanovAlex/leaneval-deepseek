import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Additive.AP

open scoped BigOperators

/-- Translating the argument of a sum over a finite abelian group does not change the sum. -/
lemma sum_add_right {G : Type*} [AddCommGroup G] [Fintype G] (g : G → ℝ) (s : G) :
    ∑ a : G, g (a + s) = ∑ x : G, g x := by
  rw [← Equiv.sum_comp (Equiv.addRight s) g]
  simp

/-- Summing a function of the total of a tuple over a finite abelian group: the map
`y ↦ ∑ i, y i` from `Fin (n+1) → G` to `G` is a uniform cover, so the sum equals
`|G|^n` times the sum over `G`. -/
theorem sum_of_coordinates {G : Type*} [AddCommGroup G] [Fintype G] (n : ℕ) (g : G → ℝ) :
    (∑ y : Fin (n+1) → G, g (∑ i, y i)) = (Fintype.card G : ℝ)^n * ∑ x : G, g x := by
  -- Reindex the tuple `y : Fin (n+1) → G` as the pair `(y 0, fun i => y i.succ)`.
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => G)).sum_comp
        (fun y : Fin (n+1) → G => g (∑ i, y i))]
  simp only [Fin.consEquiv_apply, Fin.sum_cons]
  -- Split the sum over the product into two nested sums.
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  trans ∑ z : Fin n → G, ∑ x : G, g x
  · exact Finset.sum_congr rfl (fun z _ => sum_add_right g (∑ i, z i))
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num

end Commons.Combinatorics.Additive.AP