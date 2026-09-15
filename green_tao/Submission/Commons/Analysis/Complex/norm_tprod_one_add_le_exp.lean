import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Filter
open scoped Topology

namespace Commons.Analysis.Complex

/-- For a summable family `f` of complex numbers the infinite product `∏' i, (1 + f i)`
satisfies `‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖)`.

Proof sketch: for a finite `s`, `‖∏ i ∈ s, (1 + f i)‖ ≤ ∏ i ∈ s, (1 + ‖f i‖) ≤
Real.exp (∑ i ∈ s, ‖f i‖)`; pass to the limit along the finsets (the product is multipliable:
`multipliable_one_add_of_summable`), using `le_of_tendsto_of_tendsto` and the continuity of `Real.exp`.
Useful existing lemmas: `Multipliable.norm_tprod`, `Real.rexp_tsum_eq_tprod`,
`Summable.summable_log_norm_one_add`, `Real.log_le_sub_one_of_pos`. -/
theorem norm_tprod_one_add_le_exp {ι : Type*} [Countable ι] (f : ι → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  have hm : Multipliable (fun i => (1 : ℂ) + f i) := multipliable_one_add_of_summable hf
  have hnorm : Multipliable (fun i => ‖(1 : ℂ) + f i‖) := hm.norm
  have hleft : Tendsto (fun s : Finset ι => ∏ i ∈ s, ‖(1 : ℂ) + f i‖) atTop
      (𝓝 (∏' i, ‖(1 : ℂ) + f i‖)) := by
    simpa [HasProd, SummationFilter.unconditional_filter] using hnorm.hasProd
  have hright : Tendsto (fun s : Finset ι => Real.exp (∑ i ∈ s, ‖f i‖)) atTop
      (𝓝 (Real.exp (∑' i, ‖f i‖))) := by
    have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖f i‖) atTop
        (𝓝 (∑' i, ‖f i‖)) := by
      simpa [HasSum, SummationFilter.unconditional_filter] using hf.hasSum
    exact (Real.continuous_exp.tendsto _).comp hsum
  have hbound : ∀ s : Finset ι, ∏ i ∈ s, ‖(1 : ℂ) + f i‖ ≤ Real.exp (∑ i ∈ s, ‖f i‖) := by
    intro s
    refine (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => by simpa using norm_add_le (1 : ℂ) (f i))).trans ?_
    exact Real.prod_one_add_le_exp_sum s (fun i => norm_nonneg _)
  calc ‖∏' i, (1 + f i)‖
      = ∏' i, ‖(1 : ℂ) + f i‖ := hm.norm_tprod
    _ ≤ Real.exp (∑' i, ‖f i‖) := le_of_tendsto_of_tendsto' hleft hright hbound

end Commons.Analysis.Complex