import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Commons.Algebra.BigOperators

attribute [local instance] Classical.decEq

lemma prod_sum_choice {ι κ : Type*} [Fintype ι] [Fintype κ] {R : Type*} [CommSemiring R]
    (x : ι → κ → R) :
    (∏ σ : ι, ∑ k : κ, x σ k) = ∑ g : ι → κ, ∏ σ : ι, x σ (g σ) := by
  exact Fintype.prod_sum (R := R) (κ := fun _ : ι => κ) (f := fun σ k => x σ k)

end Commons.Algebra.BigOperators