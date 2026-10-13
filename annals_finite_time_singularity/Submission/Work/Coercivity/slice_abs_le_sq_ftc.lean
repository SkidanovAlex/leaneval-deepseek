import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- **Radial mean-value bound.**  If a function `H` smooth on a neighbourhood of the
closed quadrant vanishes at `z = 0` along the angle `θ`, and its radial derivative
along that angle satisfies `|∂_z H(s,θ)| ≤ K·s` for `0 ≤ s ≤ z`, then
`|H(z,θ)| ≤ K·z²/2`.

This is the fundamental theorem of calculus for the `θ`-slice: `H(z,θ) = ∫₀^z ∂_z H`,
followed by `|∫ f| ≤ ∫ |f|` and monotonicity of the integral. -/
theorem slice_abs_le_sq_ftc {H : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd H) {z θ K : ℝ}
    (hθ : θ ∈ Spaces.Iθ) (hz : 0 ≤ z) (h0 : H 0 θ = 0)
    (hK : ∀ s ∈ Set.Icc 0 z, |Spaces.pz H s θ| ≤ K * s) :
    |H z θ| ≤ K * z ^ 2 / 2 := by
  -- The `θ`-slice `s ↦ H s θ` vanishes at `0`, so FTC gives `H z θ = ∫₀^z ∂_z H s θ ds`.
  have hFTC : ∫ s in (0:ℝ)..z, Spaces.pz H s θ = H z θ := by
    rw [Spaces.hardyZ_integral_pz_eq_sub H hsm hθ le_rfl hz, h0, sub_zero]
  have hcont : ContinuousOn (fun s => Spaces.pz H s θ) (Set.Icc 0 z) :=
    (Spaces.hardyZ_continuousOn_pz_slice H hsm hθ).mono fun x hx => by
      simp only [Set.mem_Ioi]; linarith [hx.1]
  have hint1 : IntervalIntegrable (fun s => |Spaces.pz H s θ|) volume 0 z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hz]
    exact hcont.abs
  have hint2 : IntervalIntegrable (fun s => K * s) volume 0 z := by
    apply ContinuousOn.intervalIntegrable
    exact (continuous_const.mul continuous_id).continuousOn
  -- `|∫ f| ≤ ∫ |f|`.
  have h1 : |H z θ| ≤ ∫ s in (0:ℝ)..z, |Spaces.pz H s θ| := by
    rw [← hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hz
  -- Monotonicity of the integral, using the pointwise hypothesis `hK`.
  have h2 : ∫ s in (0:ℝ)..z, |Spaces.pz H s θ| ≤ ∫ s in (0:ℝ)..z, K * s :=
    intervalIntegral.integral_mono_on hz hint1 hint2 fun s hs => hK s hs
  have h3 : ∫ s in (0:ℝ)..z, K * s = K * z ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  calc |H z θ| ≤ ∫ s in (0:ℝ)..z, |Spaces.pz H s θ| := h1
    _ ≤ ∫ s in (0:ℝ)..z, K * s := h2
    _ = K * z ^ 2 / 2 := h3

end Work.Coercivity
