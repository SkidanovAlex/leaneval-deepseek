import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Commons.Analysis.InfiniteSum

theorem summable_of_finset_tail_bound {f : ℂ → ℝ} (hf : ∀ u : ℂ, 0 ≤ f u)
    (hsmall : ∃ c : ℝ, ∀ s : Finset ℂ, (∀ u ∈ s, ‖u‖ ≤ 2) → ∑ u ∈ s, f u ≤ c)
    {C : ℝ} (htail : ∀ s : Finset ℂ, (∀ u ∈ s, 2 < ‖u‖) → ∑ u ∈ s, f u ≤ C) :
    Summable f := by
  obtain ⟨c, hc⟩ := hsmall
  refine summable_of_sum_le (c := c + C) hf (fun s => ?_)
  have h1 : ∑ u ∈ s.filter (fun u => ‖u‖ ≤ 2), f u ≤ c :=
    hc _ (fun u hu => (Finset.mem_filter.mp hu).2)
  have h2 : ∑ u ∈ s.filter (fun u => ¬ ‖u‖ ≤ 2), f u ≤ C :=
    htail _ (fun u hu => not_le.mp (Finset.mem_filter.mp hu).2)
  calc ∑ u ∈ s, f u
      = ∑ u ∈ s.filter (fun u => ‖u‖ ≤ 2), f u
        + ∑ u ∈ s.filter (fun u => ¬ ‖u‖ ≤ 2), f u :=
        (Finset.sum_filter_add_sum_filter_not s (fun u => ‖u‖ ≤ 2) f).symm
    _ ≤ c + C := add_le_add h1 h2

end Commons.Analysis.InfiniteSum