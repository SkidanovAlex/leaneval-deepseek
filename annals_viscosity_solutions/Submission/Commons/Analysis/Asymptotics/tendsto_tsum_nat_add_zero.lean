import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity

namespace Commons.Analysis.Asymptotics

theorem tendsto_tsum_nat_add_zero {f : ℕ → ℝ} (hf : Summable f) :
    Filter.Tendsto (fun i : ℕ => ∑' k : ℕ, f (i + k)) Filter.atTop (nhds 0) := by
  have _ := hf
  simpa only [Nat.add_comm] using tendsto_sum_nat_add f

end Commons.Analysis.Asymptotics