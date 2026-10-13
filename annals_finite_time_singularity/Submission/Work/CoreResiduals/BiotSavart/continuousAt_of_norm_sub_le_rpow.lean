import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- If `f` is Hölder continuous at `t` with exponent `a > 0` and constant `N ≥ 0`, then `f` is
continuous at `t`. -/
theorem continuousAt_of_norm_sub_le_rpow {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {N a t : ℝ} (ha : 0 < a) (hN : 0 ≤ N)
    (h : ∀ s : ℝ, ‖f s - f t‖ ≤ N * |s - t| ^ a) : ContinuousAt f t := by
  have hcont : Continuous (fun x : ℝ => x ^ a) := Real.continuous_rpow_const ha.le
  have hinner : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => |s - t|) :=
      continuous_abs.comp (continuous_id.sub (continuous_const (y := t)))
    simpa using hc.tendsto t
  have hrpow : Tendsto (fun s : ℝ => |s - t| ^ a) (𝓝 t) (𝓝 0) := by
    have := (hcont.tendsto 0).comp hinner
    rwa [Real.zero_rpow (ne_of_gt ha)] at this
  have hbound : Tendsto (fun s : ℝ => N * |s - t| ^ a) (𝓝 t) (𝓝 0) := by
    have := hrpow.const_mul N
    rwa [mul_zero] at this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun s => norm_nonneg _) (fun s => h s) hbound

end Work.CoreResiduals.BiotSavart
