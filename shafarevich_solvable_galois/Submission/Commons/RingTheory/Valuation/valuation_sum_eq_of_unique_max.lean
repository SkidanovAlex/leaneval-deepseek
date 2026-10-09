import Mathlib.RingTheory.Valuation.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

theorem valuation_sum_eq_of_unique_max {R Γ₀ : Type*} [Ring R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
    {ι : Type*} (s : Finset ι) (f : ι → R) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (h : ∀ i ∈ s, i ≠ i₀ → v (f i) < v (f i₀)) :
    v (∑ i ∈ s, f i) = v (f i₀) := by
  classical
  exact Valuation.map_sum_eq_of_lt v hi₀ (by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨his, hne⟩
    exact h i his (by simpa using hne))

end Commons.RingTheory.Valuation