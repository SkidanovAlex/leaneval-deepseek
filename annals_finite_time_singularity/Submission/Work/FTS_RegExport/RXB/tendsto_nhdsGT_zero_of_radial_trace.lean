import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS_RegExport.RXB

/-- If the radial trace `z · (u z · w z)²` tends to `0` as `z → 0⁺`, then `u z → 0`.
This uses that `w z = (1+z)²/z²`, so `(u z)² = z·(u z·w z)² · z³/(1+z)⁴` and hence
`|u z|` is the square root of a product of two quantities tending to `0`. -/
theorem tendsto_nhdsGT_zero_of_radial_trace {u : ℝ → ℝ}
    (h : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- The auxiliary factor `c z = z³/(1+z)⁴` tends to `0` as `z → 0⁺`.
  have hc : Filter.Tendsto (fun z : ℝ => z ^ 3 / (1 + z) ^ 4) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hcont : ContinuousAt (fun z : ℝ => z ^ 3 / (1 + z) ^ 4) 0 :=
      (continuousAt_id.pow 3).div ((continuousAt_const.add continuousAt_id).pow 4) (by norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- Hence the product tends to `0`.
  have hbc : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    simpa using h.mul hc
  -- Continuity of `sqrt` at `0` gives that `sqrt` of the product tends to `0`.
  have hsqrt : Filter.Tendsto
      (fun z => Real.sqrt (z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4)))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hcomp := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hbc
    rw [Real.sqrt_zero] at hcomp
    exact hcomp
  -- On `(0, ∞)` the quantity under the square root is exactly `(u z)²`.
  have hev : (fun z : ℝ => Real.sqrt (z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4)))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun z => |u z|) := by
    refine Filter.eventually_of_mem (U := Set.Ioi 0) self_mem_nhdsWithin ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hz'
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have hid : z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4) = (u z) ^ 2 := by
      rw [Work.Spaces.w]
      field_simp
    simp only [hid, Real.sqrt_sq_eq_abs]
  have habs : Filter.Tendsto (fun z => |u z|) (𝓝[>] (0 : ℝ)) (nhds 0) := hsqrt.congr' hev
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)

end Work.FTS_RegExport.RXB
