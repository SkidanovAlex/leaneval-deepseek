/-
# Joint continuity of the Newtonian potential of `∂ₜ f` (`PressureOn`)

This module proves `Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential`: for a jointly
continuous `f : ℝ³ → ℝ → ℝ³` whose time derivative `∂ₜ f` is also jointly continuous and whose
spatial support is locally uniform in time,

  `(x, t) ↦ -∫ y, ⟪nablaNfund (x - y), ∂ₜ f y t⟫`

is continuous on `ℝ³ × ℝ`.  This is the `∂_t q` half of the joint `C¹`-regularity of the pressure
`p = -‖u‖²/2 - q` of the reconstruction `PressureOn.Defs` (the potential `q` is the
`∇Nfund`-convolution of the Lamb vector, and `∂_t q` is the potential of the Lamb vector's time
derivative).

## Proof

The kernel `nablaNfund z = (4π‖z‖³)⁻¹ • z` is *not* integrable on `ℝ³` (its size is
`‖nablaNfund z‖ = (4π)⁻¹‖z‖⁻²`, marginal in dimension three), but the integrand has *locally
uniformly compact support*: for `t` in a fixed neighbourhood of `t₀` the field `∂ₜ f (·, t)` is
supported in the ball of radius `R` supplied by the hypothesis `hsupp` (support is inherited by the
time derivative: `timeDeriv_support`), and it is bounded by a constant `M` on that ball
(`exists_bound_strip`).  After the change of variables `z = x - y`
(`integral_shift_nablaNfund`) the integrand is therefore dominated, for `(x, t)` near any given
point, by the *fixed* integrable function

  `z ↦ (4π)⁻¹ M ‖z‖⁻² 1_{B(0, R + ‖x₀‖ + 1)}(z)`

(`integrable_inv_normSq_indicator_closedBall`).  Since the integrand is also measurable in `z` for
each `(x,t)` and continuous at each fixed `z`, the dominated convergence theorem for filters
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) gives continuity at every point.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.timeDeriv_support
import Submission.Work.FTS.PressureOn.exists_bound_strip
import Submission.Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Metric Bornology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## Elementary facts about the kernel `∇Nfund` -/

/-- `(a³)⁻¹ · a ≤ (a²)⁻¹` for `a ≥ 0`; equality holds for `a > 0`. -/
private lemma inv_pow_three_mul_le (a : ℝ) (ha : 0 ≤ a) : (a ^ 3)⁻¹ * a ≤ (a ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; norm_num
  · refine le_of_eq ?_
    field_simp

/-- Pointwise size of the gradient of the fundamental solution:
`‖nablaNfund z‖ ≤ (4π)⁻¹‖z‖⁻²` (the value at `z = 0` is `0`, so the inequality holds there too). -/
private lemma norm_nablaNfund_le (z : R3) :
    ‖nablaNfund z‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have h : ‖nablaNfund z‖ = ‖newtonGrad z‖ := by
    rw [nablaNfund_eq_neg_newtonGrad, norm_neg]
  rw [h, norm_newtonGrad]
  have h2 : (‖z‖ ^ 3)⁻¹ * ‖z‖ ≤ (‖z‖ ^ 2)⁻¹ := inv_pow_three_mul_le ‖z‖ (norm_nonneg z)
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The kernel is Borel measurable. -/
private lemma measurable_nablaNfund : Measurable (fun z : R3 => nablaNfund z) := by
  unfold nablaNfund
  have h1 : Measurable (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹) := by fun_prop
  exact h1.smul measurable_id

/-! ## The change of variables `z = x - y` -/

/-- **The kernel integral is a convolution**: shifting the integration variable `y ↦ z = x - y`
(which preserves Lebesgue measure) turns the defining form of the potential into its convolution
form. -/
theorem integral_shift_nablaNfund (g : R3 → R3) (x : R3) :
    ∫ y, inner ℝ (nablaNfund (x - y)) (g y) = ∫ z, inner ℝ (nablaNfund z) (g (x - z)) := by
  set Φ : R3 → ℝ := fun z => inner ℝ (nablaNfund z) (g (x - z)) with hΦ
  have h1 : (fun y => inner ℝ (nablaNfund (x - y)) (g y)) = fun y => Φ (-(y - x)) := by
    funext y
    simp only [hΦ, neg_sub, sub_sub_cancel]
  rw [h1, MeasureTheory.integral_sub_right_eq_self (fun w => Φ (-w)) x,
    MeasureTheory.integral_neg_eq_self Φ volume]

/-! ## Joint continuity in the shifted form -/

/-- **Joint continuity of the shifted `∇Nfund`-integral.**  For a jointly continuous
`g : ℝ³ → ℝ → ℝ³` whose spatial support is locally uniformly bounded in time, the map
`(x, t) ↦ ∫ z, ⟪∇Nfund z, g (x - z) t⟫` is continuous on `ℝ³ × ℝ`.

The proof is dominated convergence: near a fixed `(x₀, t₀)` the integrand is dominated by the
integrable model function `z ↦ (4π)⁻¹ M ‖z‖⁻² 1_{B(0, R+‖x₀‖+1)}(z)`, where `R` is the uniform
support radius and `M` a uniform bound for `g` on the strip `B(0,R) × [t₀-1/2, t₀+1/2]`. -/
theorem continuous_shifted_integral_joint {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2)
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, g x s ≠ 0 → ‖x‖ ≤ R) :
    Continuous fun p : R3 × ℝ => ∫ z, inner ℝ (nablaNfund z) (g (p.1 - z) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₀⟩
  obtain ⟨R, hR⟩ := hsupp t₀
  obtain ⟨M, hM0, hM⟩ := exists_bound_strip hg R t₀
  have hInt : Integrable (fun z : R3 => (4 * Real.pi)⁻¹ * M *
      ((‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) volume := by
    have h1 := integrable_inv_normSq_indicator_closedBall (R + ‖x₀‖ + 1)
    have h2 : (fun z : R3 => (4 * Real.pi)⁻¹ * M *
          ((‖z‖ ^ 2)⁻¹ *
            (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z))
        = fun z : R3 => ((4 * Real.pi)⁻¹ * M) *
          ((‖z‖ ^ 2)⁻¹ *
            (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z) := by
      funext z; ring
    rw [h2]
    exact h1.const_mul _
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝 (x₀, t₀))
    (fun z : R3 => (4 * Real.pi)⁻¹ * M * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) ?_ ?_ hInt ?_
  · -- a.e. strong measurability of the integrand, for every `(x,t)`
    filter_upwards with p
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_nablaNfund.inner (hg.measurable.comp
      ((continuous_const.sub continuous_id).prodMk continuous_const).measurable)
  · -- pointwise domination by the fixed integrable model function
    filter_upwards [Metric.ball_mem_nhds (x₀, t₀) (by norm_num : (0 : ℝ) < 1 / 2)] with p hp
    refine Eventually.of_forall fun z => ?_
    have hd : max (dist p.1 x₀) (dist p.2 t₀) < 1 / 2 := by
      rwa [Metric.mem_ball, Prod.dist_eq] at hp
    have hp1 : ‖p.1 - x₀‖ < 1 / 2 := by
      have h : dist p.1 x₀ < 1 / 2 := lt_of_le_of_lt (le_max_left _ _) hd
      rwa [dist_eq_norm] at h
    have hp2lt : |p.2 - t₀| < 1 / 2 := by
      have h : dist p.2 t₀ < 1 / 2 := lt_of_le_of_lt (le_max_right _ _) hd
      rwa [Real.dist_eq] at h
    obtain ⟨hp2lo, hp2hi⟩ := abs_lt.mp hp2lt
    have hp2Ioo : p.2 ∈ Set.Ioo (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
    have hp2Icc : p.2 ∈ Set.Icc (t₀ - 1 / 2) (t₀ + 1 / 2) := ⟨by linarith, by linarith⟩
    by_cases hz : g (p.1 - z) p.2 = 0
    · rw [hz, inner_zero_right, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hM0)
        (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) z))
    · -- `g (p.1 - z) p.2 ≠ 0` puts `z` in a fixed ball
      have hzR : ‖p.1 - z‖ ≤ R := hR p.2 hp2Ioo (p.1 - z) hz
      have hx1 : ‖p.1‖ ≤ ‖x₀‖ + 1 / 2 := by
        have h2 : ‖p.1‖ = ‖(p.1 - x₀) + x₀‖ := by rw [sub_add_cancel]
        rw [h2]
        linarith [norm_add_le (p.1 - x₀) x₀]
      have hzx : ‖z‖ ≤ R + ‖x₀‖ + 1 := by
        have h2 : ‖z‖ = ‖(z - p.1) + p.1‖ := by rw [sub_add_cancel]
        rw [h2]
        have h3 : ‖z - p.1‖ = ‖p.1 - z‖ := norm_sub_rev z p.1
        linarith [norm_add_le (z - p.1) p.1]
      have hzball : z ∈ Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1) := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzx
      have hmem : p.1 - z ∈ Metric.closedBall (0 : R3) R := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzR
      rw [Set.indicator_of_mem hzball, mul_one]
      calc ‖inner ℝ (nablaNfund z) (g (p.1 - z) p.2)‖
          ≤ ‖nablaNfund z‖ * ‖g (p.1 - z) p.2‖ := norm_inner_le_norm _ _
        _ ≤ ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * M :=
            mul_le_mul (norm_nablaNfund_le z) (hM (p.1 - z) hmem p.2 hp2Icc)
              (norm_nonneg _) (by positivity)
        _ = (4 * Real.pi)⁻¹ * M * (‖z‖ ^ 2)⁻¹ := by ring
  · -- pointwise convergence of the integrand, at every fixed `z`
    filter_upwards with z
    exact (continuous_const.inner (hg.comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd))).continuousAt

/-- **Joint continuity of the pressure potential of a locally uniformly supported field.**  For a
jointly continuous `g : ℝ³ → ℝ → ℝ³` whose spatial support is locally uniform in time, the map
`p ↦ pressurePotential (g · p.2) p.1` is continuous on `ℝ³ × ℝ`.

This is the general form of the continuity statement needed for the pressure reconstruction of
`PressureOn.Defs`; it is `continuous_shifted_integral_joint` transported back to the defining
(unshifted) form of `pressurePotential` by `integral_shift_nablaNfund`. -/
theorem continuous_pressurePotential_joint_of_supported {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2)
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, g x s ≠ 0 → ‖x‖ ≤ R) :
    Continuous fun p : R3 × ℝ => pressurePotential (fun y => g y p.2) p.1 := by
  have hcont := continuous_shifted_integral_joint hg hsupp
  have hfun : (fun p : R3 × ℝ => pressurePotential (fun y => g y p.2) p.1)
      = fun p : R3 × ℝ => -(∫ z, inner ℝ (nablaNfund z) (g (p.1 - z) p.2)) := by
    funext p
    rw [pressurePotential_apply]
    congr 1
    exact integral_shift_nablaNfund (fun y => g y p.2) p.1
  rw [hfun]
  exact hcont.neg

/-! ## The target theorem -/

/-- **Joint continuity of the Newtonian potential of `∂ₜ f`.**  If `f` and `timeDeriv f` are
jointly continuous and the spatial support of `f` is locally uniform in time, then
`(x,t) ↦ -∫ y, ⟪∇Nfund (x-y), ∂ₜ f y t⟫` is continuous on `ℝ³ × ℝ`.

(`hf` is not needed: the only place where the spatial field `f` itself enters is the support
hypothesis, which `∂ₜ f` inherits — `timeDeriv_support`.) -/
theorem continuous_timeDeriv_pressurePotential {f : R3 → ℝ → R3}
    (hf : Continuous fun p : R3 × ℝ => f p.1 p.2)
    (hd : Continuous fun p : R3 × ℝ => FiniteTimeSingularity.timeDeriv f p.1 p.2)
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, f x s ≠ 0 → ‖x‖ ≤ R) :
    Continuous fun p : R3 × ℝ =>
      (-∫ y, inner ℝ (nablaNfund (p.1 - y)) (FiniteTimeSingularity.timeDeriv f y p.2)) := by
  -- the time derivative inherits the support hypothesis
  have hsupp' := timeDeriv_support hsupp
  -- `hf` is not needed for the conclusion; recorded here so that it is visibly accounted for
  have _hf' := hf
  -- joint continuity of the potential of the (time-differentiated) field
  have hmain := continuous_pressurePotential_joint_of_supported hd hsupp'
  simpa only [pressurePotential_apply] using hmain

end Work.FTS.PressureOn
