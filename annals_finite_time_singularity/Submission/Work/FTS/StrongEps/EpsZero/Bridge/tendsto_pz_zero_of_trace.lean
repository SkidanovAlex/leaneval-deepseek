import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open Filter

/-- **A radial trace bound forces the radial derivative to vanish at the axis.**  If
`z * (Dz f z θ * w z) ^ 2 → 0` as `z → 0⁺` then `pz f z θ → 0` as `z → 0⁺`.
For `z > 0` one has `Dz f z θ = z * pz f z θ` and `w z = (1+z)^2 / z^2`, hence
`z * (Dz f z θ * w z) ^ 2 = (pz f z θ)^2 * (1+z)^4 / z`; since `z ≤ (1+z)^4` for `z ≥ 0`
this gives `(pz f z θ)^2 ≤ z * (Dz f z θ * w z) ^ 2`, and the claim follows by a squeeze
argument plus the continuity of `Real.sqrt` at `0`. -/
theorem tendsto_pz_zero_of_trace {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (h : Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ))) :
    Filter.Tendsto (fun z : ℝ => Work.Spaces.pz f z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
  refine squeeze_zero_norm'
    (a := fun z : ℝ => Real.sqrt (z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)) ?_ ?_
  · -- For `z > 0` the trace dominates `(pz f z θ)²`, so `|pz f z θ| ≤ √(trace)`.
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzpos : 0 < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hkey : z * (z * Work.Spaces.pz f z θ * ((1 + z) ^ 2 / z ^ 2)) ^ 2
        = (Work.Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 4 / z) := by
      field_simp
    have hmain : (Work.Spaces.pz f z θ) ^ 2
        ≤ z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2 := by
      simp only [Work.Spaces.Dz, Work.Spaces.w]
      rw [hkey]
      calc (Work.Spaces.pz f z θ) ^ 2
          = (Work.Spaces.pz f z θ) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 4 / z) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            rw [le_div_iff₀ hzpos]
            have hge1 : (1 : ℝ) ≤ 1 + z := by linarith
            have hp : (1 + z) ≤ (1 + z) ^ 4 := by
              simpa using pow_le_pow_right₀ hge1 (show (1 : ℕ) ≤ 4 by norm_num)
            linarith
    simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt hmain
  · -- `√` is continuous at `0`, where it takes the value `0`.
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h

end Work.FTS.StrongEps.EpsZero.Bridge
