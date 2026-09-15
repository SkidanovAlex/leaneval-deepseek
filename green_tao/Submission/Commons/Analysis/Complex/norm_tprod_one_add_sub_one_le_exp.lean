import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace Commons.Analysis.Complex

open Filter
open scoped Topology

/-- For a summable family `f` of complex numbers, the infinite product `∏' i, (1 + f i)` differs
from `1` by at most `Real.exp (∑' i, ‖f i‖) - 1`. -/
theorem norm_tprod_one_add_sub_one_le_exp {ι : Type*} [Countable ι] (f : ι → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    ‖(∏' i, (1 + f i)) - 1‖ ≤ Real.exp (∑' i, ‖f i‖) - 1 := by
  have hm : Multipliable (fun i => (1 : ℂ) + f i) := multipliable_one_add_of_summable hf
  have hprod : Tendsto (fun s : Finset ι => ∏ i ∈ s, ((1 : ℂ) + f i)) atTop
      (𝓝 (∏' i, (1 + f i))) := by
    simpa [HasProd, SummationFilter.unconditional_filter] using hm.hasProd
  have hleft : Tendsto (fun s : Finset ι => ‖(∏ i ∈ s, ((1 : ℂ) + f i)) - 1‖) atTop
      (𝓝 (‖(∏' i, (1 + f i)) - 1‖)) := by
    have hc : Continuous fun x : ℂ => ‖x - 1‖ := by fun_prop
    exact (hc.tendsto _).comp hprod
  have hright : Tendsto (fun s : Finset ι => Real.exp (∑ i ∈ s, ‖f i‖) - 1) atTop
      (𝓝 (Real.exp (∑' i, ‖f i‖) - 1)) := by
    have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖f i‖) atTop
        (𝓝 (∑' i, ‖f i‖)) := by
      simpa [HasSum, SummationFilter.unconditional_filter] using hf.hasSum
    have hc : Continuous fun x : ℝ => Real.exp x - 1 := by fun_prop
    exact (hc.tendsto _).comp hsum
  exact le_of_tendsto_of_tendsto' hleft hright fun s => Finset.norm_prod_one_add_sub_one_le s f

end Commons.Analysis.Complex
