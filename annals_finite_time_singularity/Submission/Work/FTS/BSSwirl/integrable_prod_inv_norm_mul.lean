/-
# `Work.FTS.BSSwirl.integrable_prod_inv_norm_mul`

The Newtonian kernel `‖x - y‖⁻¹` is locally integrable in `ℝ³` (`∫_{B(0,R)} ‖z‖⁻¹ dz = 2πR²`,
the exponent `-1` being above the threshold `-3` of dimension `3`), so multiplying it by a
*measurable, bounded, compactly supported* function on `ℝ³ × ℝ³` keeps us inside `L¹`:

`p ↦ ‖p.1 - p.2‖⁻¹ * g p` is `Integrable (volume.prod volume)` whenever `g` is a.e. strongly
measurable, bounded by `C`, and supported in `K × L` with `K`, `L` compact.

## Proof

Let `κ p = ‖p.1 - p.2‖⁻¹ · 1_K p.1 · 1_L p.2`.  Two facts give the result:

* `κ` is integrable.  It is measurable, and its `lintegral` is finite: since the indicators are
  `0/1`-valued, `ofReal κ` is the product of the three `ofReal`s, so Tonelli computes the
  integral as an iterated one; for `x ∈ K` the inner integral is bounded by `2π (R_L + R_K + 1)²`
  (the ball `B(0, R_L)` sits inside `B(x, R_L + R_K + 1)`; translate it to the origin and
  integrate the radial power `‖z‖⁻¹ = ‖z‖ ^ (-1)` there) — that one-variable estimate is the
  separate lemma `Work.FTS.BSSwirl.lintegral_inv_norm_mul_ball_indicator_le` — and the outer
  integral is that constant times `volume K < ⊤`.
* `p ↦ ‖p.1 - p.2‖⁻¹ * g p` agrees pointwise with `κ p * g p`: where `g p ≠ 0` the support
  hypothesis forces `p ∈ K × L`, hence the indicators equal `1`; where `g p = 0` both sides
  vanish.  The claim then follows from `Integrable.bdd_mul` (integrating `κ` against the bounded
  a.e. strongly measurable `g`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.lintegral_inv_norm_mul_ball_indicator_le
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

/-- **Finiteness of the `lintegral` of the Newtonian kernel on `K × L`.**  For compact `K`, `L`
the `ℝ≥0∞`-valued integral of `‖x - y‖⁻¹ 1_{K×L}(x,y)` is finite. -/
private lemma lintegral_prod_inv_norm_indicator_lt_top {K L : Set R3} (hK : IsCompact K)
    (hL : IsCompact L) :
    ∫⁻ p : R3 × R3, ENNReal.ofReal ((‖p.1 - p.2‖)⁻¹ *
        (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
      ∂(volume.prod volume) < ⊤ := by
  classical
  obtain ⟨rK, hrK⟩ := (Metric.isBounded_iff_subset_closedBall (0 : R3)).mp hK.isBounded
  obtain ⟨rL, hrL⟩ := (Metric.isBounded_iff_subset_closedBall (0 : R3)).mp hL.isBounded
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hLmeas : MeasurableSet L := hL.isClosed.measurableSet
  -- radii of balls containing `K` and `L`
  obtain ⟨A, hA0, hKsub⟩ : ∃ A : ℝ, 0 ≤ A ∧ K ⊆ Metric.closedBall (0 : R3) A :=
    ⟨max rK 0, le_max_right _ _, fun x hx =>
      Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp (hrK hx)) (le_max_left _ _))⟩
  obtain ⟨B, hB0, hLsub⟩ : ∃ B : ℝ, 0 ≤ B ∧ L ⊆ Metric.closedBall (0 : R3) B :=
    ⟨max rL 0, le_max_right _ _, fun x hx =>
      Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp (hrL hx)) (le_max_left _ _))⟩
  -- the inner (`y`-)integral is bounded by `c`
  have hinner_le : ∀ x : R3, ‖x‖ ≤ A →
      (∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
          ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y))
        ≤ ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2) := by
    intro x hx
    refine le_trans ?_ (lintegral_inv_norm_mul_ball_indicator_le x hB0 hx)
    have hstep : ∀ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
          ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y)
        ≤ ENNReal.ofReal (‖x - y‖⁻¹) *
          ENNReal.ofReal
            (((Metric.closedBall (0 : R3) B).indicator (fun _ => (1 : ℝ))) y) := by
      intro y
      by_cases hy : y ∈ L
      · exact le_of_eq (by
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hLsub hy), ENNReal.ofReal_one])
      · rw [Set.indicator_of_notMem hy, ENNReal.ofReal_zero, mul_zero]
        exact zero_le
    exact lintegral_mono hstep
  -- the pointwise rewriting of `ofReal` of the product
  have hpoint : ∀ p : R3 × R3,
      ENNReal.ofReal ((‖p.1 - p.2‖)⁻¹ * (K.indicator (fun _ => (1 : ℝ))) p.1 *
          (L.indicator (fun _ => (1 : ℝ))) p.2)
        = ENNReal.ofReal (‖p.1 - p.2‖⁻¹) *
            ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) p.1) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) p.2) := by
    intro p
    have h1 : (0 : ℝ) ≤ (‖p.1 - p.2‖⁻¹) * (K.indicator (fun _ => (1 : ℝ))) p.1 :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
  -- measurability of the product form
  have hmeas : Measurable (fun p : R3 × R3 => ENNReal.ofReal (‖p.1 - p.2‖⁻¹) *
        ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) p.1) *
        ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) p.2)) :=
    ((((continuous_fst.sub continuous_snd).norm.measurable.inv).ennreal_ofReal).mul
      ((measurable_const.indicator hKmeas).ennreal_ofReal.comp measurable_fst)).mul
      ((measurable_const.indicator hLmeas).ennreal_ofReal.comp measurable_snd)
  -- the pointwise bound for the iterated integrand
  have hinner_bound : ∀ x : R3,
      (∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
          ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
          ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y))
        ≤ ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
          ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2) := by
    intro x
    by_cases hx : x ∈ K
    · have hxnorm : ‖x‖ ≤ A := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hKsub hx)
      have hstep : ∀ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y)
          = ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) := by
        intro y
        rw [Set.indicator_of_mem hx, ENNReal.ofReal_one, mul_one]
      rw [lintegral_congr hstep, Set.indicator_of_mem hx, ENNReal.ofReal_one, one_mul]
      exact hinner_le x hxnorm
    · have hzero : (∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y)) = 0 := by
        have hstep : ∀ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
              ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
              ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) = 0 := by
          intro y
          rw [Set.indicator_of_notMem hx, ENNReal.ofReal_zero, mul_zero, zero_mul]
        rw [lintegral_congr hstep]
        simp
      rw [hzero]
      exact zero_le
  -- the pointwise bound for the outer integrand
  have houter_bound : ∀ x : R3,
      ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
          ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2)
        = (K.indicator (fun _ => ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2))) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, ENNReal.ofReal_one, one_mul, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, ENNReal.ofReal_zero, zero_mul,
        Set.indicator_of_notMem hx]
  calc ∫⁻ p : R3 × R3, ENNReal.ofReal ((‖p.1 - p.2‖)⁻¹ *
        (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
      ∂(volume.prod volume)
      = ∫⁻ x : R3, ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) := by
        rw [lintegral_congr hpoint]
        exact lintegral_prod _ hmeas.aemeasurable
    _ ≤ ∫⁻ x : R3, ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
          ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2) :=
        lintegral_mono hinner_bound
    _ = ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2) * volume K := by
        rw [← lintegral_indicator_const hKmeas
          (ENNReal.ofReal (2 * Real.pi * (B + A + 1) ^ 2))]
        exact lintegral_congr houter_bound
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem integrable_prod_inv_norm_mul
    {g : Work.FTS.BSSwirl.R3 × Work.FTS.BSSwirl.R3 → ℝ}
    (hgmeas : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.prod MeasureTheory.volume))
    {C : ℝ} {K L : Set Work.FTS.BSSwirl.R3} (hK : IsCompact K) (hL : IsCompact L)
    (hbdd : ∀ p, ‖g p‖ ≤ C) (hsupp : ∀ p, g p ≠ 0 → p.1 ∈ K ∧ p.2 ∈ L) :
    MeasureTheory.Integrable (fun p : Work.FTS.BSSwirl.R3 × Work.FTS.BSSwirl.R3 => (‖p.1 - p.2‖)⁻¹ * g p)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hLmeas : MeasurableSet L := hL.isClosed.measurableSet
  -- the dominating kernel `κ` is integrable
  have hκ_meas : Measurable (fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ *
      (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2) :=
    ((((continuous_fst.sub continuous_snd).norm.measurable.inv).mul
      ((measurable_const.indicator hKmeas).comp measurable_fst)).mul
      ((measurable_const.indicator hLmeas).comp measurable_snd))
  have hκ_int : Integrable (fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ *
      (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
      (volume.prod volume) := by
    refine ⟨hκ_meas.aestronglyMeasurable, ?_⟩
    refine (MeasureTheory.hasFiniteIntegral_iff_ofReal
        (f := fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ * (K.indicator (fun _ => (1 : ℝ))) p.1 *
          (L.indicator (fun _ => (1 : ℝ))) p.2) ?_).mpr
        (lintegral_prod_inv_norm_indicator_lt_top hK hL)
    exact Filter.Eventually.of_forall fun p =>
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  -- `g p * κ p = ‖p.1 - p.2‖⁻¹ * g p` everywhere
  have hfinal : ∀ p : R3 × R3, g p * ((‖p.1 - p.2‖)⁻¹ *
      (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
        = (‖p.1 - p.2‖)⁻¹ * g p := by
    intro p
    by_cases hp : g p = 0
    · rw [hp, zero_mul, mul_zero]
    · obtain ⟨h1, h2⟩ := hsupp p hp
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, mul_one, mul_one]
      ring
  exact (hκ_int.bdd_mul hgmeas (Filter.Eventually.of_forall hbdd)).congr
    (Filter.Eventually.of_forall fun p => by
      show g p * ((‖p.1 - p.2‖)⁻¹ * (K.indicator (fun _ => (1 : ℝ))) p.1 *
        (L.indicator (fun _ => (1 : ℝ))) p.2) = (‖p.1 - p.2‖)⁻¹ * g p
      exact hfinal p)

end Work.FTS.BSSwirl
