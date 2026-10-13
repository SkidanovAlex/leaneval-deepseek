import Mathlib

namespace Work.WilE3.Taylor.Grad

open Filter Set
open scoped Topology

theorem tendsto_rpow_nhdsGT_zero_of_pos {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun t : ℝ => t ^ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- `t ↦ t ^ (-s)` blows up as `t → 0⁺` since `-s < 0`; inverting gives the limit `0`,
  -- and on `t > 0` we have `(t ^ (-s))⁻¹ = t ^ s`.
  have hneg : -s < 0 := by linarith
  have h1 : Tendsto (fun t : ℝ => (t ^ (-s))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_rpow_neg_nhdsGT_zero hneg).inv_tendsto_atTop
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.rpow_neg (le_of_lt ht), inv_inv]

end Work.WilE3.Taylor.Grad
