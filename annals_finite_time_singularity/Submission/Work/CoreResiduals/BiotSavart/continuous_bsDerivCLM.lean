/-
# `Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM` — continuity of the Biot–Savart derivative

The main result of this file is

`continuous_bsDerivCLM : Continuous (fun x => bsDerivCLM ω ρ x)`

for a vorticity `ω` that is bounded and `c`-Hölder with `c > 0`.  The proof is the standard
"peel off the singularity" argument, organised around the dominated-convergence theorem
`MeasureTheory.continuousOn_of_dominated`:

* `bsIntegrand ω x a = (crossL (ω a - ω x)).comp (kDerivCLM (x - a))` is the integrand of the
  Bochner integral defining `bsDerivCLM ω ρ x` (`IntegrandDefs`), and it obeys the pointwise bound
  `‖bsIntegrand ω x a‖ ≤ 4 C ‖x - a‖^{c-3}` (`norm_bsIntegrand_le`);
* splitting the integral over `B(0,ρ)` into the *inner* part over `B(x₀,Δ)` and the *outer* part
  (`integral_split`), the inner part is bounded, uniformly in `x ∈ B(x₀,Δ/2)`, by
  `4C(4π/c)(3Δ/2)^c` (`norm_setIntegral_le_inner`, via the radial integral
  `integral_ball_sub_norm_rpow`), which tends to `0` as `Δ → 0⁺`;
* the outer part is continuous at `x₀` by dominated convergence, with the dominating function
  `a ↦ K (1 + ‖a‖^{c-3})` supplied by `exists_rpow_dom_bound` and integrated with
  `integrableOn_one_add_norm_rpow_ball` (`continuousOn_outer`);
* the `ε`-`δ` bookkeeping combines the two `ContinuousAt` statements, while the algebraic shape
  term `(4π/3) • crossL (ω x)` is continuous because `ω` is (`continuous_of_holder`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.exists_rpow_dom_bound
import Submission.Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-! ## Elementary consequences of the Hölder hypothesis -/

/-- A `c`-Hölder field with `c > 0` and nonnegative Hölder constant is continuous. -/
theorem continuous_of_holder {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) : Continuous ω := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto ω (𝓝 x) (𝓝 (ω x))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (f := fun y : R3 => dist (ω y) (ω x))
    (g := fun y : R3 => C * ‖y - x‖ ^ c) (fun y : R3 => dist_nonneg) (fun y => ?_) ?_
  · simpa only [dist_eq_norm] using hhold y x
  · have h1 : Tendsto (fun y : R3 => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have hsub : ContinuousAt (fun y : R3 => y - x) x := continuousAt_id.sub continuousAt_const
      have h : Tendsto (fun y : R3 => ‖y - x‖) (𝓝 x) (𝓝 ((fun y : R3 => ‖y - x‖) x)) :=
        (continuous_norm.continuousAt.comp hsub).tendsto
      simpa using h
    have h2 : Tendsto (fun y : R3 => ‖y - x‖ ^ c) (𝓝 x) (𝓝 ((0 : ℝ) ^ c)) :=
      h1.rpow_const (Or.inr hc.le)
    rw [Real.zero_rpow hc.ne'] at h2
    have h3 := h2.const_mul C
    simpa using h3

/-- A point `a` outside the ball `B(x₀,Δ)` is at distance at least `Δ/2` from any point of
`B(x₀,Δ/2)`. -/
lemma le_norm_sub_of_notMem_ball {x₀ x a : R3} {Δ : ℝ} (hx : ‖x - x₀‖ ≤ Δ / 2)
    (ha : a ∉ Metric.ball x₀ Δ) : Δ / 2 ≤ ‖x - a‖ := by
  have h1 : Δ ≤ ‖a - x₀‖ := by
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at ha
    simpa only [norm_sub_rev] using ha
  have h2 : ‖a - x₀‖ ≤ ‖a - x‖ + ‖x - x₀‖ := by
    have heq : a - x₀ = (a - x) + (x - x₀) := by abel
    rw [heq]
    exact norm_add_le _ _
  calc Δ / 2 ≤ ‖a - x₀‖ - ‖x - x₀‖ := by linarith
    _ ≤ ‖a - x‖ := by linarith
    _ = ‖x - a‖ := norm_sub_rev _ _

/-- Membership in `B(x₀,Δ/2)` in terms of the norm. -/
lemma norm_sub_le_of_mem_ball {x₀ x : R3} {Δ : ℝ} (hx : x ∈ Metric.ball x₀ (Δ / 2)) :
    ‖x - x₀‖ ≤ Δ / 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  exact le_of_lt hx

/-- A point of `B(x₀,Δ/2)` has norm at most `‖x₀‖ + 1` when `Δ ≤ 2`. -/
lemma norm_le_of_mem_ball_half {x₀ x : R3} {Δ : ℝ} (hΔ2 : Δ ≤ 2) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖x‖ ≤ ‖x₀‖ + 1 := by
  have h := norm_add_le (x - x₀) x₀
  rw [sub_add_cancel] at h
  calc ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := h
    _ ≤ ‖x₀‖ + 1 := by linarith

/-- The ball `B(x₀,Δ)` is contained in `B(x,3Δ/2)` for `x ∈ B(x₀,Δ/2)`. -/
lemma ball_subset_ball_three_halves {x₀ x : R3} {Δ : ℝ} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    Metric.ball x₀ Δ ⊆ Metric.ball x (3 * Δ / 2) := by
  intro a ha
  rw [Metric.mem_ball] at ha ⊢
  have h2 : dist x₀ x ≤ Δ / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hx
  have h3 := dist_triangle a x₀ x
  linarith

/-- `B(0,ρ) ∩ B(x₀,Δ) ⊆ B(x,3Δ/2)` for `x ∈ B(x₀,Δ/2)`. -/
lemma inter_ball_subset_ball_three_halves {x₀ x : R3} {Δ ρ : ℝ}
    (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ) ⊆ Metric.ball x (3 * Δ / 2) :=
  subset_trans Set.inter_subset_right (ball_subset_ball_three_halves hx)

/-! ## Integrability of the singular kernel and of the two pieces of the integral -/

/-- `a ↦ ‖a - x‖ ^ (c - 3)` is integrable on `B(x,R)` when `c > 0`. -/
theorem integrableOn_norm_sub_rpow_ball (x : R3) {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    IntegrableOn (fun a : R3 => (‖a - x‖ : ℝ) ^ (c - 3)) (Metric.ball x R) volume := by
  have hΘ : -3 < c - 3 := by linarith
  have hval := integral_ball_sub_norm_rpow x R (c - 3) hΘ hR
  have hpos : 0 < 4 * Real.pi * R ^ ((c - 3) + 3) / ((c - 3) + 3) := by
    rw [show (c - 3) + 3 = c from by ring]
    positivity
  by_contra hcon
  have h0 := integral_undef hcon
  rw [hval] at h0
  exact absurd h0 (ne_of_gt hpos)

/-- The *inner* piece of the integrand is integrable: on `B(0,ρ) ∩ B(x₀,Δ)` it is dominated by
the integrable singular kernel `4C‖· - x‖^{c-3}`. -/
theorem integrableOn_bsIntegrand_inter {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    IntegrableOn (bsIntegrand ω x) ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hInt : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume :=
    ((integrableOn_norm_sub_rpow_ball x hc h3Δ).mono_set
      (inter_ball_subset_ball_three_halves hx)).const_mul (4 * C)
  refine Integrable.mono' hInt ((aestronglyMeasurable_bsIntegrand hω x).mono_measure
    Measure.restrict_le_self) (Filter.Eventually.of_forall fun a => ?_)
  simpa only [norm_sub_rev] using norm_bsIntegrand_le hC hhold x a

/-- **Weighted domination of the outer integrand.**  For `x ∈ B(x₀,Δ/2)` and any `a`, the
truncated integrand `1_{B(0,ρ)\\B(x₀,Δ)} • bsIntegrand ω x` is dominated by the weight
`K(1 + ‖a‖^{c-3})` on `B(0,ρ)`. -/
lemma bsIntegrand_indicator_le {ω : R3 → R3} {C c K Δ ρ : ℝ} {x₀ x : R3} (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (hK : ∀ x a : R3, ‖x‖ ≤ ‖x₀‖ + 1 → Δ / 2 ≤ ‖x - a‖ →
      4 * C * (‖x - a‖ : ℝ) ^ (c - 3) ≤ K * (1 + (‖a‖ : ℝ) ^ (c - 3)))
    (hK0 : 0 ≤ K) (hΔ2 : Δ ≤ 2) (hx : ‖x - x₀‖ ≤ Δ / 2) (a : R3) :
    ‖((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator (bsIntegrand ω x) a‖ ≤
      (Metric.ball (0 : R3) ρ).indicator (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) a := by
  by_cases ha : a ∈ (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)
  · rw [Set.indicator_of_mem ha (bsIntegrand ω x),
      Set.indicator_of_mem ha.1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
    exact le_trans (norm_bsIntegrand_le hC hhold x a)
      (hK x a (norm_le_of_mem_ball_half hΔ2 hx) (le_norm_sub_of_notMem_ball hx ha.2))
  · rw [Set.indicator_of_notMem ha (bsIntegrand ω x)]
    by_cases ha1 : a ∈ Metric.ball (0 : R3) ρ
    · rw [Set.indicator_of_mem ha1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
      simpa using mul_nonneg hK0 (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (Real.rpow_nonneg (norm_nonneg a) (c - 3)))
    · rw [Set.indicator_of_notMem ha1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
      simp

theorem integrableOn_bsIntegrand_ssub {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    IntegrableOn (bsIntegrand ω x) ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) volume := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hdom : Integrable
      ((Metric.ball (0 : R3) ρ).indicator fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  refine (integrable_indicator_iff hmeas).mp (Integrable.mono' hdom
    ((aestronglyMeasurable_bsIntegrand hω x).indicator hmeas)
    (Filter.Eventually.of_forall fun a => bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ)
      (x₀ := x₀) hC hhold hK hK0 hΔ2 hx a))

/-! ## The three estimates -/

/-- **The inner piece is small.**  Uniformly for `x ∈ B(x₀,Δ/2)`, the integral of the integrand
over `B(0,ρ) ∩ B(x₀,Δ)` is bounded by `4C(4π/c)(3Δ/2)^c`, which tends to `0` as `Δ → 0⁺`. -/
theorem norm_setIntegral_le_inner {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
      ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c := by
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hsub := inter_ball_subset_ball_three_halves (ρ := ρ) hx
  have hIntX : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      (Metric.ball x (3 * Δ / 2)) volume :=
    (integrableOn_norm_sub_rpow_ball x hc h3Δ).const_mul (4 * C)
  have hint : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume := hIntX.mono_set hsub
  calc ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
      ≤ ∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ),
          4 * C * (‖a - x‖ : ℝ) ^ (c - 3) :=
        MeasureTheory.norm_integral_le_of_norm_le hint
          (Filter.Eventually.of_forall fun a =>
            (by simpa only [norm_sub_rev] using norm_bsIntegrand_le hC hhold x a))
    _ ≤ ∫ a in Metric.ball x (3 * Δ / 2), 4 * C * (‖a - x‖ : ℝ) ^ (c - 3) :=
        setIntegral_mono_set hIntX
          (Filter.Eventually.of_forall fun a =>
            mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (norm_nonneg _) _))
          (Filter.Eventually.of_forall fun a ha => hsub ha)
    _ = 4 * C * ∫ a in Metric.ball x (3 * Δ / 2), (‖a - x‖ : ℝ) ^ (c - 3) := by
        rw [integral_const_mul]
    _ = 4 * C * (4 * Real.pi * (3 * Δ / 2) ^ ((c - 3) + 3) / ((c - 3) + 3)) := by
        rw [integral_ball_sub_norm_rpow x (3 * Δ / 2) (c - 3) (by linarith) h3Δ]
    _ = 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c := by
        rw [show (c - 3) + 3 = c from by ring]
        field_simp
        try ring

/-- **The outer piece is continuous.**  The integral of the integrand over `B(0,ρ) \ B(x₀,Δ)` is
continuous on `B(x₀,Δ/2)`: away from the singular diagonal it is dominated by an integrable
weight and it is continuous in the parameter at every point `a ≠ x`. -/
theorem continuousOn_outer {ω : R3 → R3} (hω : Continuous ω) {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) :
    ContinuousOn (fun x : R3 => ∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ),
      bsIntegrand ω x a) (Metric.ball x₀ (Δ / 2)) := by
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  have key : ContinuousOn (fun x : R3 => ∫ a,
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator (bsIntegrand ω x) a)
      (Metric.ball x₀ (Δ / 2)) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun a : R3 =>
        (Metric.ball (0 : R3) ρ).indicator (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) a)
      (F := fun x a => ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator
        (bsIntegrand ω x) a)
      (s := Metric.ball x₀ (Δ / 2)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (aestronglyMeasurable_bsIntegrand hω x).indicator hmeas
    · intro x hx
      have hx' : ‖x - x₀‖ ≤ Δ / 2 := norm_sub_le_of_mem_ball hx
      exact Filter.Eventually.of_forall fun a =>
        bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ) (x₀ := x₀) hC hhold hK hK0 hΔ2 hx' a
    · exact (integrable_indicator_iff measurableSet_ball).mpr
        ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
    · refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)
      · have hcont : ContinuousOn (fun x : R3 => bsIntegrand ω x a) (Metric.ball x₀ (Δ / 2)) := by
          intro x hx
          have hx' : ‖x - x₀‖ ≤ Δ / 2 := norm_sub_le_of_mem_ball hx
          have hne : a ≠ x := by
            intro h
            have h2 := le_norm_sub_of_notMem_ball hx' ha.2
            rw [h, sub_self, norm_zero] at h2
            linarith [hΔ]
          exact (continuousAt_bsIntegrand hω hne).continuousWithinAt
        exact ContinuousOn.congr hcont fun x hx => Set.indicator_of_mem ha (bsIntegrand ω x)
      · have hconst : ContinuousOn (fun _ : R3 => (0 : R3 →L[ℝ] R3)) (Metric.ball x₀ (Δ / 2)) :=
          continuousOn_const
        refine ContinuousOn.congr hconst fun x hx => ?_
        exact Set.indicator_of_notMem ha (bsIntegrand ω x)
  simpa only [MeasureTheory.integral_indicator hmeas] using key

/-- **The splitting identity.**  The integral over `B(0,ρ)` is the sum of its parts over
`B(0,ρ) ∩ B(x₀,Δ)` and `B(0,ρ) \ B(x₀,Δ)`. -/
theorem integral_split {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      = (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
        + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a) := by
  have hdisj : Disjoint ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ))
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact hb.2 ha.2
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  have h1 : (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      = ∫ a in ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ))
          ∪ ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)), bsIntegrand ω x a := by
    rw [Set.inter_union_sdiff]
  rw [h1]
  exact setIntegral_union hdisj hmeas (integrableOn_bsIntegrand_inter hc hC hhold x₀ hΔ hx)
    (integrableOn_bsIntegrand_ssub hc hC hhold x₀ hΔ hΔ2 hx)

/-! ## The main theorem -/

/-- **Continuity of the candidate derivative of the Biot–Savart field.**  For a `c`-Hölder
vorticity with `c > 0` and nonnegative Hölder constant, `x ↦ bsDerivCLM ω ρ x` is continuous. -/
theorem continuous_bsDerivCLM_of_nonneg {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (ρ : ℝ) :
    Continuous (fun x => bsDerivCLM ω ρ x) := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  have hshape : Continuous (fun x : R3 => (4 * Real.pi / 3) • crossL (ω x)) :=
    (continuous_crossL.comp hω).const_smul (4 * Real.pi / 3)
  rw [continuous_iff_continuousAt]
  intro x₀
  change ContinuousAt (fun x : R3 =>
    (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a) + (4 * Real.pi / 3) • crossL (ω x)) x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  -- the modulus of the inner piece tends to `0`
  have hlim : ContinuousAt (fun Δ : ℝ => 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c) 0 := by
    have hlin : ContinuousAt (fun Δ : ℝ => 3 * Δ / 2) 0 := by fun_prop
    have hrpow : ContinuousAt (fun t : ℝ => t ^ c) (3 * 0 / 2) := by
      simpa using Real.continuousAt_rpow_const (0 : ℝ) c (Or.inr hc.le)
    have h1 : ContinuousAt (fun Δ : ℝ => (3 * Δ / 2) ^ c) 0 :=
      (ContinuousAt.comp (x := (0 : ℝ)) (f := fun Δ : ℝ => 3 * Δ / 2)
        (g := fun t : ℝ => t ^ c) hrpow hlin)
    exact h1.const_mul _
  obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hlim (ε / 4) hε4
  set Δ : ℝ := min 1 (r / 2) with hΔdef
  have hΔpos : 0 < Δ := lt_min one_pos (by linarith)
  have hΔle1 : Δ ≤ 1 := min_le_left _ _
  have hΔle2 : Δ ≤ 2 := by linarith
  have hLnn : 0 ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hΔsmall : 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c < ε / 4 := by
    have hdist : dist Δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hΔpos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h0 : 4 * C * (4 * Real.pi / c) * (3 * 0 / 2) ^ c = 0 := by
      rw [show (3 * 0 / 2 : ℝ) = 0 from by norm_num, Real.zero_rpow hc.ne']
      ring
    have h := hr hdist
    rw [Real.dist_eq, h0, sub_zero, abs_of_nonneg hLnn] at h
    exact h
  -- the outer piece is continuous at `x₀`
  have hOutC : ContinuousOn (fun x : R3 =>
      ∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
      (Metric.ball x₀ (Δ / 2)) := continuousOn_outer hω hc hC hhold x₀ hΔpos hΔle2
  have hOutAt := hOutC.continuousAt (Metric.ball_mem_nhds x₀ (by linarith))
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.continuousAt_iff.mp hOutAt (ε / 4) hε4
  obtain ⟨r₃, hr₃pos, hr₃⟩ :=
    Metric.continuousAt_iff.mp (hshape.continuousAt (x := x₀)) (ε / 4) hε4
  refine ⟨min (Δ / 2) (min r₂ r₃), by positivity, fun x hx => ?_⟩
  have hxΔ : ‖x - x₀‖ ≤ Δ / 2 := by
    have h1 : dist x x₀ < Δ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    rw [dist_eq_norm] at h1
    exact le_of_lt h1
  have hx₂ : dist x x₀ < r₂ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have hx₃ : dist x x₀ < r₃ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have hInX := norm_setIntegral_le_inner (ρ := ρ) hc hC hhold x₀ hΔpos hxΔ
  have hInx₀ := norm_setIntegral_le_inner (ρ := ρ) (x := x₀) hc hC hhold x₀ hΔpos
    (by simp only [sub_self, norm_zero]; positivity)
  have hIx := integral_split (ρ := ρ) hc hC hhold x₀ hΔpos hΔle2 hxΔ
  have hIx₀ := integral_split (ρ := ρ) (x := x₀) hc hC hhold x₀ hΔpos hΔle2
    (by simp only [sub_self, norm_zero]; positivity)
  have hOut := hr₂ hx₂
  have hShape := hr₃ hx₃
  have hinner : ‖(∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)‖ < 3 * (ε / 4) := by
    rw [hIx, hIx₀]
    have hOutdiff : ‖(∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
        - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖
        < ε / 4 := by
      rw [← dist_eq_norm]
      exact hOut
    have hcombine : ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a))
        - ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
        = ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
          + ((∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)) := by
      abel
    rw [hcombine]
    calc ‖((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
              - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
            + ((∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
              - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))‖
        ≤ ‖(∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖
          + ‖(∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖ :=
          norm_add_le _ _
      _ ≤ (‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
            + ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a‖)
          + ε / 4 := by
          have h2 := norm_sub_le
            (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)
          linarith
      _ < 3 * (ε / 4) := by linarith
  have hshape' : ‖(4 * Real.pi / 3) • crossL (ω x)
      - (4 * Real.pi / 3) • crossL (ω x₀)‖ < ε / 4 := by
    rw [← dist_eq_norm]
    exact hShape
  calc dist ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
          + (4 * Real.pi / 3) • crossL (ω x))
        ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
          + (4 * Real.pi / 3) • crossL (ω x₀))
      = ‖((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
            + (4 * Real.pi / 3) • crossL (ω x))
          - ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀))‖ := dist_eq_norm _ _
    _ ≤ ‖(∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
            - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)‖
          + ‖(4 * Real.pi / 3) • crossL (ω x) - (4 * Real.pi / 3) • crossL (ω x₀)‖ := by
        have heq : ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
              + (4 * Real.pi / 3) • crossL (ω x))
            - ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
              + (4 * Real.pi / 3) • crossL (ω x₀))
            = ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
                - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a))
              + ((4 * Real.pi / 3) • crossL (ω x) - (4 * Real.pi / 3) • crossL (ω x₀)) := by
          abel
        rw [heq]
        exact norm_add_le _ _
    _ < ε := by linarith

/-- **Continuity of the candidate derivative of the Biot–Savart field** for a bounded Hölder
vorticity.  The case of a negative Hölder constant is reduced to the nonnegative one: then
`ω` is constant (the Hölder inequality would otherwise force a positive norm to be negative),
and then `bsIntegrand` vanishes identically. -/
theorem continuous_bsDerivCLM {ω : Work.LWP.R3 → Work.LWP.R3} {M C c : ℝ} (hc : 0 < c)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (ρ : ℝ) : Continuous (fun x => Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x) := by
  have hCmax : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ max C 0 * ‖a - b‖ ^ c := by
    intro a b
    rcases le_or_gt 0 C with hC | hC
    · simpa only [max_eq_left hC] using hhold a b
    · have hconst : ω a = ω b := by
        by_cases hab : a = b
        · rw [hab]
        · exfalso
          have hpos : 0 < ‖a - b‖ ^ c :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) c
          have hneg : C * ‖a - b‖ ^ c < 0 := mul_neg_of_neg_of_pos hC hpos
          linarith [norm_nonneg (ω a - ω b), hhold a b]
      rw [hconst, sub_self, norm_zero, max_eq_right (le_of_lt hC)]
      simp
  exact continuous_bsDerivCLM_of_nonneg (C := max C 0) hc (le_max_right _ _) hCmax ρ

end Work.CoreResiduals.BiotSavart
