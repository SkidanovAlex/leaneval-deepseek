import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Topology Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1.HJ

theorem jetZsliceTendsto {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (hJet : Work.FTS.Regularity.Jet α S N h) (hα : 0 < α) {θ τ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    Filter.Tendsto (fun z : ℝ => h z θ τ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h 0 θ τ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun z : ℝ => N * z ^ α)
    (Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : (0:ℝ) ≤ z := le_of_lt hz
    have hb := hJet.zmod hz0 (le_refl (0:ℝ)) hθ hτ
    rw [Real.norm_eq_abs]
    rw [sub_zero, abs_of_nonneg hz0] at hb
    exact hb
  · have hcont : Continuous fun z : ℝ => N * z ^ α :=
      continuous_const.mul (Real.continuous_rpow_const hα.le)
    have h0 : N * (0:ℝ) ^ α = 0 := by
      rw [Real.zero_rpow (ne_of_gt hα), mul_zero]
    simpa [h0] using hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds

end Work.FTS_RegExport.RXR1.HJ
