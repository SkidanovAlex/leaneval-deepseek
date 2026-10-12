import Mathlib.Analysis.Normed.Order.Lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Tails

theorem exists_finset_sum_le_of_summable {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    (hf0 : ∀ i, 0 ≤ f i) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : Finset ι, ∀ S : Finset ι, Disjoint S s₀ → ∑ i ∈ S, f i ≤ ε := by
  obtain ⟨s₀, hs₀⟩ := hf.vanishing (isOpen_Iio.mem_nhds hε)
  exact ⟨s₀, fun S hS => le_of_lt (hs₀ S hS)⟩

end Work.BoseRowsL.Tails
