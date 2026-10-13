/-
# The mass kernel is an approximate identity of total mass `-1`

This module proves

`∫ x, massKernel ε x * Ψ x → -Ψ 0` as `ε → 0⁺`

for every `C¹` function `Ψ`.  The proof has four ingredients.

* `massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)` is a *radial* function of `‖x‖`
  (`massKernel_eq_mkRad`); integrating it against a radial weight uses the polar-coordinate
  formula `integral_radial` of the sibling module.
* `massKernel ε` is continuous and supported in the shrinking ball `‖x‖ ≤ √2 ε`
  (`continuous_massKernel`, `hasCompactSupport_massKernel`, `massKernel_eq_zero_of_lt`),
  hence integrable (`integrable_massKernel`).
* its total mass is `-1`, independently of `ε` (`integral_massKernel`), and its total
  variation is bounded uniformly in `ε` (`integral_abs_massKernel_le`).
* `Ψ` is continuous at `0`, so `Ψ - Ψ 0` is uniformly small on that shrinking ball.

The final argument is then a two-line `ε`-`δ` computation.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.integral_radial
import Submission.Work.FTS.PressureOn.PoissonAux.mk_profile

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology Metric
open scoped Topology ENNReal NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## The radial profile of the mass kernel -/

/-- The mass kernel as a function of `‖x‖`: `mkRad ε r = (4πr)⁻¹ ρ_ε''(r)`. -/
noncomputable def mkRad (ε : ℝ) (r : ℝ) : ℝ :=
  (4 * Real.pi * r)⁻¹ * deriv (deriv (rhoProfile ε)) r

theorem massKernel_eq_mkRad (ε : ℝ) (x : R3) : massKernel ε x = mkRad ε ‖x‖ := rfl

/-- The mass kernel vanishes outside the shrinking ball `‖x‖ ≤ √2 ε`. -/
theorem massKernel_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {x : R3}
    (hx : Real.sqrt 2 * ε < ‖x‖) : massKernel ε x = 0 := by
  rw [massKernel_eq_mkRad, mkRad,
    mk_deriv_deriv_rhoProfile_eq_zero hε (Or.inr (by rwa [abs_of_nonneg (norm_nonneg x)])),
    mul_zero]

/-! ## Continuity -/

theorem continuousAt_mkRad (ε : ℝ) (hε : 0 < ε) (r : ℝ) : ContinuousAt (mkRad ε) r := by
  by_cases hr : |r| < ε
  · have h : mkRad ε =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have hpos : 0 < ε - |r| := by linarith
      filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have hs' : |s| < ε := by
        have h1 : |s - r| < ε - |r| := hs
        have h2 : |s| ≤ |s - r| + |r| := by
          calc |s| = |s - r + r| := by ring_nf
            _ ≤ |s - r| + |r| := abs_add_le (s - r) r
        linarith
      rw [mkRad, mk_deriv_deriv_rhoProfile_eq_zero hε (Or.inl hs'), mul_zero]
    exact continuousAt_const.congr h.symm
  · have hr0 : r ≠ 0 := by
      intro h
      rw [h, abs_zero] at hr
      linarith
    have hX : ContinuousAt (fun s : ℝ => deriv (deriv (rhoProfile ε)) s) r :=
      (mk_continuous_deriv_deriv_rhoProfile ε).continuousAt
    have hinv : ContinuousAt (fun s : ℝ => (4 * Real.pi * s)⁻¹) r := by
      refine ContinuousAt.inv₀ (continuousAt_const.mul continuousAt_id) ?_
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr0
    change ContinuousAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ * deriv (deriv (rhoProfile ε)) s) r
    exact hinv.mul hX

theorem continuous_mkRad (ε : ℝ) (hε : 0 < ε) : Continuous (mkRad ε) :=
  continuous_iff_continuousAt.mpr fun r => continuousAt_mkRad ε hε r

theorem continuous_massKernel (ε : ℝ) (hε : 0 < ε) : Continuous (massKernel ε) := by
  have h : massKernel ε = fun x : R3 => mkRad ε ‖x‖ := funext (massKernel_eq_mkRad ε)
  rw [h]
  exact (continuous_mkRad ε hε).comp continuous_norm

/-! ## Compact support and integrability -/

theorem hasCompactSupport_massKernel (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (massKernel ε) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (Real.sqrt 2 * ε)) (isCompact_closedBall 0 _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (massKernel_eq_zero_of_lt hε (lt_of_not_ge h))

theorem integrable_massKernel (ε : ℝ) (hε : 0 < ε) : Integrable (massKernel ε) :=
  (continuous_massKernel ε hε).integrable_of_hasCompactSupport (hasCompactSupport_massKernel ε hε)

theorem integrable_massKernel_mul (ε : ℝ) (hε : 0 < ε) {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Integrable (fun x : R3 => massKernel ε x * Ψ x) := by
  refine ((continuous_massKernel ε hε).mul hΨ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (Real.sqrt 2 * ε)) (isCompact_closedBall 0 _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  refine hx (by
    show massKernel ε x * Ψ x = 0
    rw [massKernel_eq_zero_of_lt hε (lt_of_not_ge h), zero_mul])

/-! ## The total mass `∫ massKernel ε = -1` -/

theorem integral_massKernel (ε : ℝ) (hε : 0 < ε) : ∫ x : R3, massKernel ε x = -1 := by
  have hpt : ∀ r : ℝ, r ^ 2 * mkRad ε r
      = (4 * Real.pi)⁻¹ * (r * deriv (deriv (rhoProfile ε)) r) := by
    intro r
    rw [mkRad]
    rcases eq_or_ne r 0 with h | h
    · rw [h]
      simp
    · calc r ^ 2 * ((4 * Real.pi * r)⁻¹ * deriv (deriv (rhoProfile ε)) r)
          = (4 * Real.pi)⁻¹ * (r ^ 2 * r⁻¹) * deriv (deriv (rhoProfile ε)) r := by
            rw [mul_inv]
            ring
        _ = (4 * Real.pi)⁻¹ * r * deriv (deriv (rhoProfile ε)) r := by
            rw [show r ^ 2 * r⁻¹ = r by
              rw [sq, mul_assoc, mul_inv_cancel₀ h, mul_one]]
        _ = (4 * Real.pi)⁻¹ * (r * deriv (deriv (rhoProfile ε)) r) := by ring
  rw [show massKernel ε = fun x : R3 => mkRad ε ‖x‖ from funext (massKernel_eq_mkRad ε)]
  rw [integral_radial (mkRad ε)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hpt r), integral_const_mul,
    mk_integral_mul_deriv_deriv_rhoProfile ε hε]
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  field_simp

/-! ## The uniform bound on the total variation -/

theorem integral_abs_massKernel_le {B : ℝ} (hB0 : 0 ≤ B) (ε : ℝ) (hε : 0 < ε)
    (hB : ∀ r : ℝ, |deriv (deriv (rhoProfile ε)) r| ≤ B / ε ^ 2) :
    ∫ x : R3, |massKernel ε x| ≤ 100 * B := by
  have hpi : 0 < 4 * Real.pi := by positivity
  have hc : 0 ≤ B / (4 * Real.pi * ε ^ 3) := by positivity
  have hC : ∀ x : R3, |massKernel ε x| ≤ B / (4 * Real.pi * ε ^ 3) := by
    intro x
    by_cases hx : ‖x‖ < ε
    · have hz : massKernel ε x = 0 := by
        rw [massKernel_eq_mkRad, mkRad,
          mk_deriv_deriv_rhoProfile_eq_zero hε (Or.inl (by rwa [abs_of_nonneg (norm_nonneg x)])),
          mul_zero]
      rw [hz, abs_zero]
      positivity
    · push Not at hx
      rw [massKernel_eq_mkRad, mkRad, abs_mul]
      have h1 : |(4 * Real.pi * ‖x‖)⁻¹| = (4 * Real.pi * ‖x‖)⁻¹ := by
        rw [abs_of_nonneg]
        positivity
      rw [h1]
      have h2 := hB ‖x‖
      have h3 : (4 * Real.pi * ‖x‖)⁻¹ * (B / ε ^ 2) ≤ B / (4 * Real.pi * ε ^ 3) := by
        have h4 : (4 * Real.pi * ‖x‖)⁻¹ ≤ (4 * Real.pi * ε)⁻¹ := by
          rw [inv_le_inv₀ (mul_pos hpi (lt_of_lt_of_le hε hx)) (mul_pos hpi hε)]
          nlinarith
        have h5 : 0 ≤ B / ε ^ 2 := by positivity
        calc (4 * Real.pi * ‖x‖)⁻¹ * (B / ε ^ 2)
            ≤ (4 * Real.pi * ε)⁻¹ * (B / ε ^ 2) := mul_le_mul_of_nonneg_right h4 h5
          _ = B / (4 * Real.pi * ε ^ 3) := by
              field_simp
      exact le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
  have hvol : (volume : Measure R3).real (Metric.closedBall 0 (Real.sqrt 2 * ε))
      ≤ (volume : Measure R3).real (Metric.ball 0 (4 * ε)) := by
    rw [Measure.real_def, Measure.real_def]
    refine ENNReal.toReal_mono (measure_ball_ne_top (μ := volume) (x := (0 : R3)) (r := 4 * ε))
      (measure_mono ?_)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : Real.sqrt 2 < 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [norm_nonneg x, hε]
  have hball : (volume : Measure R3).real (Metric.ball 0 (4 * ε)) = 256 * Real.pi * ε ^ 3 / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 4 * ε),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 * ε) ^ 3),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  calc ∫ x : R3, |massKernel ε x|
      ≤ ∫ x : R3, (Metric.closedBall 0 (Real.sqrt 2 * ε)).indicator
          (fun _ => B / (4 * Real.pi * ε ^ 3)) x := by
        refine integral_mono_ae (integrable_massKernel ε hε).abs ?_ ?_
        · refine (integrableOn_const (μ := volume) (s := Metric.closedBall 0 (Real.sqrt 2 * ε))
            (C := B / (4 * Real.pi * ε ^ 3))
            (measure_closedBall_lt_top (μ := volume) (x := (0 : R3))
              (r := Real.sqrt 2 * ε)).ne).integrable_indicator measurableSet_closedBall
        · refine Eventually.of_forall fun x => ?_
          by_cases hxo : x ∈ Metric.closedBall 0 (Real.sqrt 2 * ε)
          · rw [Set.indicator_of_mem hxo]
            exact hC x
          · rw [Set.indicator_of_notMem hxo]
            have hz : massKernel ε x = 0 := by
              rw [Metric.mem_closedBall, dist_zero_right] at hxo
              rw [massKernel_eq_zero_of_lt hε (lt_of_not_ge hxo)]
            show |massKernel ε x| ≤ 0
            rw [hz, abs_zero]
    _ = (volume : Measure R3).real (Metric.closedBall 0 (Real.sqrt 2 * ε))
          * (B / (4 * Real.pi * ε ^ 3)) := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
    _ ≤ (volume : Measure R3).real (Metric.ball 0 (4 * ε)) * (B / (4 * Real.pi * ε ^ 3)) :=
        mul_le_mul_of_nonneg_right hvol hc
    _ = (256 * Real.pi * ε ^ 3 / 3) * (B / (4 * Real.pi * ε ^ 3)) := by rw [hball]
    _ = B * 64 / 3 := by
        field_simp
        ring
    _ ≤ 100 * B := by linarith

/-! ## The limit -/

theorem tendsto_integral_massKernel_mul {Ψ : R3 → ℝ} (hΨ : ContDiff ℝ 1 Ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, massKernel ε x * Ψ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-(Ψ 0))) := by
  obtain ⟨B, hB0, hB⟩ := mk_exists_bound_deriv_deriv_rhoProfile
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨η, hη0, hη⟩ :=
    Metric.continuousAt_iff.mp hΨ.continuous.continuousAt (δ / (100 * (B + 1)))
      (by positivity)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < η / Real.sqrt 2)] with ε hεball
  intro hεpos
  have hε : 0 < ε := hεpos
  have hBε := hB ε hε
  have hδ' : 0 < δ / (100 * (B + 1)) := by positivity
  have hεη : Real.sqrt 2 * ε < η := by
    have h1 : |ε| < η / Real.sqrt 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hεball
    have h2 : ε < η / Real.sqrt 2 := (abs_lt.mp h1).2
    have h3 : Real.sqrt 2 * (η / Real.sqrt 2) = η := by
      field_simp
    have h4 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hmain : (∫ x : R3, massKernel ε x * Ψ x) + Ψ 0
      = ∫ x : R3, massKernel ε x * (Ψ x - Ψ 0) := by
    have hsplit : ∫ x : R3, massKernel ε x * (Ψ x - Ψ 0)
        = ∫ x : R3, (massKernel ε x * Ψ x - massKernel ε x * Ψ 0) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hsplit, integral_sub (integrable_massKernel_mul ε hε hΨ.continuous)
      ((integrable_massKernel ε hε).mul_const (Ψ 0)), integral_mul_const, integral_massKernel ε hε]
    ring
  have hae : ∀ᵐ x ∂(volume : Measure R3),
      |massKernel ε x * (Ψ x - Ψ 0)| ≤ |massKernel ε x| * (δ / (100 * (B + 1))) := by
    refine Eventually.of_forall fun x => ?_
    by_cases hx : massKernel ε x = 0
    · simp [hx]
    · have hxnorm : ‖x‖ ≤ Real.sqrt 2 * ε := by
        by_contra h
        exact hx (massKernel_eq_zero_of_lt hε (lt_of_not_ge h))
      have hdist : dist x 0 < η := by
        rw [dist_zero_right]
        linarith
      have hΨx : |Ψ x - Ψ 0| ≤ δ / (100 * (B + 1)) :=
        le_of_lt (by simpa [Real.dist_eq] using hη hdist)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hΨx (abs_nonneg _)
  have habs : |∫ x : R3, massKernel ε x * (Ψ x - Ψ 0)|
      ≤ ∫ x : R3, |massKernel ε x * (Ψ x - Ψ 0)| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun x : R3 => massKernel ε x * (Ψ x - Ψ 0))
  have hle1 : |∫ x : R3, massKernel ε x * (Ψ x - Ψ 0)|
      ≤ ∫ x : R3, |massKernel ε x| * (δ / (100 * (B + 1))) := by
    refine le_trans habs (integral_mono_ae
      (integrable_massKernel_mul ε hε (hΨ.continuous.sub continuous_const)).abs ?_ hae)
    exact ((integrable_massKernel ε hε).abs).mul_const _
  rw [Real.dist_eq, show (∫ x : R3, massKernel ε x * Ψ x) - (-(Ψ 0))
      = (∫ x : R3, massKernel ε x * Ψ x) + Ψ 0 by ring, hmain]
  calc |∫ x : R3, massKernel ε x * (Ψ x - Ψ 0)|
      ≤ ∫ x : R3, |massKernel ε x| * (δ / (100 * (B + 1))) := hle1
    _ = (∫ x : R3, |massKernel ε x|) * (δ / (100 * (B + 1))) := integral_mul_const _ _
    _ ≤ (100 * B) * (δ / (100 * (B + 1))) :=
        mul_le_mul_of_nonneg_right (integral_abs_massKernel_le hB0 ε hε hBε) (le_of_lt hδ')
    _ = B * δ / (B + 1) := by
        field_simp
    _ < δ := by
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < B + 1)]
        nlinarith

end Work.FTS.PressureOn.PoissonAux
