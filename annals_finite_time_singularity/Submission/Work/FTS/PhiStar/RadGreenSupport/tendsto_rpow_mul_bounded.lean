import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.RadGreenSupport

/-- If `f` is bounded by `B ≥ 0` on the positive half-line, then `t ^ r * f t → 0` as
`t → 0⁺` for every real exponent `r > 0`. -/
theorem tendsto_rpow_mul_bounded {f : ℝ → ℝ} {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hfb : ∀ t : ℝ, 0 < t → |f t| ≤ B) :
    Filter.Tendsto (fun t : ℝ => t ^ r * f t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hrpow : Filter.Tendsto (fun t : ℝ => t ^ r) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    have h := (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    simpa [Real.zero_rpow hr.ne'] using h
  have hmain : Filter.Tendsto (fun t : ℝ => |t ^ r * f t|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    refine squeeze_zero' (g := fun t : ℝ => t ^ r * B)
      (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0 r)]
      exact mul_le_mul_of_nonneg_left (hfb t ht) (Real.rpow_nonneg ht0 r)
    · have h := hrpow.mul (tendsto_const_nhds (x := B))
      simpa using h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact hmain

end Work.FTS.PhiStar.RadGreenSupport
