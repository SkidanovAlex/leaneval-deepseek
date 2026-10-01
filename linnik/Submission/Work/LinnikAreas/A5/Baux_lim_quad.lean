import Mathlib

namespace Work.LinnikAreas.A5

open Filter Asymptotics
open scoped Topology

theorem Baux_lim_quad :
    Filter.Tendsto (fun t : ℝ => (t - 1 + Real.exp (-t)) / t ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / 2)) := by
  -- `Real.exp x = 1 + x + x²/2 + o(x²)` near `0`, from Mathlib's Taylor expansion of `exp`.
  have hlittle0 : (fun x : ℝ => Real.exp x - 1 - x - x ^ 2 / 2) =o[𝓝 (0 : ℝ)] (· ^ 2) := by
    have h := Real.exp_sub_sum_range_succ_isLittleO_pow 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, pow_zero,
      pow_one, zero_add, div_one] at h
    rw [show (fun x : ℝ => Real.exp x - (1 + x + x ^ 2 / 2))
          = (fun x : ℝ => Real.exp x - 1 - x - x ^ 2 / 2) from funext (fun x => by ring)] at h
    exact h
  -- Substitute `x ↦ -t`.
  have hlittle : (fun t : ℝ => Real.exp (-t) - 1 - (-t) - (-t) ^ 2 / 2)
      =o[𝓝 (0 : ℝ)] (fun t => t ^ 2) := by
    have h := hlittle0.comp_tendsto (show Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 0) by
      simpa using tendsto_neg (0 : ℝ))
    simpa [Function.comp_def] using h
  -- Restrict to the right-neighbourhood of `0`.
  have hlittle' : (fun t : ℝ => Real.exp (-t) - 1 - (-t) - (-t) ^ 2 / 2)
      =o[𝓝[Set.Ioi 0] (0 : ℝ)] (fun t => t ^ 2) :=
    hlittle.mono nhdsWithin_le_nhds
  have hquot : Tendsto (fun t : ℝ => (Real.exp (-t) - 1 - (-t) - (-t) ^ 2 / 2) / t ^ 2)
      (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := hlittle'.tendsto_div_nhds_zero
  -- Rewrite the difference quotient in the shape of the target, minus `1/2`.
  have hmain : Tendsto (fun t : ℝ => (t - 1 + Real.exp (-t)) / t ^ 2 - 1 / 2)
      (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ hquot
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
    ring
  have h2 := hmain.add (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := 𝓝[Set.Ioi 0] (0 : ℝ)))
  simpa [sub_add_cancel] using h2

end Work.LinnikAreas.A5
