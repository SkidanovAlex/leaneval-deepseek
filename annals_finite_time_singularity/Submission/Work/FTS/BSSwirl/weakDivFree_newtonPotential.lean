import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.integrableOn_inv_norm_sub_closedBall
import Submission.Work.FTS.BSSwirl.convolution_inv_norm_fderiv
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory Set Filter Topology
open scoped Topology Convolution ENNReal

noncomputable section

/-!
# `Work.FTS.BSSwirl.weakDivFree_newtonPotential` — `div ω = 0` weakly implies `div (A ω) = 0` weakly

For a bounded, a.e. strongly measurable field `ω : ℝ³ → ℝ³` supported in `closedBall 0 R` whose
distributional divergence vanishes (`WeakDivFree ω`), the same holds for its vector Newtonian
potential `A ω x = (4π)⁻¹ ∫ ‖x - y‖⁻¹ • ω y dy`:
`WeakDivFree (newtonPotential ω)`.  This is the weak identity `div (Δ⁻¹ ω) = Δ⁻¹ (div ω) = 0`.

For a smooth compactly supported test function `k` the proof is

```
∫_x ⟪A ω x, ∇k x⟫
  = (4π)⁻¹ ∫_x ∫_y ‖x - y‖⁻¹ * (fderiv ℝ k x) (ω y)          [definition + pull the integral out]
  = (4π)⁻¹ ∫_y ∫_x ‖x - y‖⁻¹ * (fderiv ℝ k x) (ω y)          [Fubini]
  = (4π)⁻¹ ∫_y (fderiv ℝ G y) (ω y)                          [convolution calculus: G = k ⋆ ‖·‖⁻¹]
  = (4π)⁻¹ ∫_y ⟪ω y, ∇(χ G) y⟫                               [χ ≡ 1 near supp ω]
  = 0,                                                        [WeakDivFree ω, χ G smooth, cs]
```

where `G y = ∫_x ‖y - x‖⁻¹ k x dx` is the (scalar) Newtonian potential of the test function: it is
`C^∞` because it is the convolution of a compactly supported smooth function with the locally
integrable kernel `‖·‖⁻¹`, and its derivative is the potential of the derivative
(`convolution_inv_norm_fderiv`).  The cutoff `χ y = smoothTransition ((R+1)² + 1 - ‖y‖²)` makes
`χ G` compactly supported so that the weak condition applies.

The two ingredients proved elsewhere are `Work.FTS.BSSwirl.integrableOn_inv_norm_sub_closedBall`
(local integrability of `‖· - c‖⁻¹`) and `Work.FTS.BSSwirl.convolution_inv_norm_fderiv` (the
derivative of the Newtonian potential of a test function).  The Fubini input — joint integrability
of `‖x - y‖⁻¹ * (fderiv ℝ k x) (ω y)` — is proved in this file.

## Joint integrability of the Newtonian kernel against a bounded compactly supported
measurable function on `ℝ³ × ℝ³`

The Fubini step below needs
`Integrable (fun p : ℝ³ × ℝ³ => ‖p.1 - p.2‖⁻¹ * g p) (volume.prod volume)` for `g` measurable,
bounded and supported in `K × L` with `K`, `L` compact.  Since `‖x - y‖⁻¹` is locally integrable
in dimension three, this holds; the proof below dominates `g` by its support indicators and
computes the resulting `ℝ≥0∞`-integral by Tonelli, using the radial ball integral
`∫_{B(0,r)} ‖z‖ ^ s = 4π r^{s+3}/(s+3)` of `Work.CoreResiduals.BiotSavart`. -/

/-- For `‖x‖ ≤ A` and `r ≥ 0`, the `ℝ≥0∞`-integral of `‖x - y‖⁻¹` against the indicator of
`closedBall 0 r` is at most `ofReal (4 π (r + A + 1)^{(-1)+3} / ((-1)+3))`. -/
private lemma lintegral_inv_norm_mul_indicator_ball_le (x : R3) {r A : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ A) :
    ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
        ENNReal.ofReal ((Metric.closedBall (0 : R3) r).indicator (fun _ => (1 : ℝ)) y)
      ≤ ENNReal.ofReal (4 * Real.pi * (r + A + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)) := by
  have hB : MeasurableSet (Metric.closedBall (0 : R3) r) :=
    Metric.isClosed_closedBall.measurableSet
  have hA0 : 0 ≤ A := le_trans (norm_nonneg x) hx
  have hρ : (0 : ℝ) < r + A + 1 := by linarith
  have hsub : Metric.closedBall (0 : R3) r ⊆ Metric.ball x (r + A + 1) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
      _ ≤ r + A := add_le_add hy hx
      _ < r + A + 1 := by linarith
  have hpt : ∀ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
        ENNReal.ofReal ((Metric.closedBall (0 : R3) r).indicator (fun _ => (1 : ℝ)) y)
      = (Metric.closedBall (0 : R3) r).indicator
          (fun y => ENNReal.ofReal (‖x - y‖⁻¹)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) r
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ENNReal.ofReal_one, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero, mul_zero]
  calc ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
        ENNReal.ofReal ((Metric.closedBall (0 : R3) r).indicator (fun _ => (1 : ℝ)) y)
      = ∫⁻ y : R3, (Metric.closedBall (0 : R3) r).indicator
          (fun y => ENNReal.ofReal (‖x - y‖⁻¹)) y := lintegral_congr hpt
    _ = ∫⁻ y in Metric.closedBall (0 : R3) r, ENNReal.ofReal (‖x - y‖⁻¹) :=
        lintegral_indicator hB _
    _ ≤ ∫⁻ y in Metric.ball x (r + A + 1), ENNReal.ofReal (‖x - y‖⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.ball x (r + A + 1), ENNReal.ofReal (‖y - x‖⁻¹) := by
        refine lintegral_congr fun y => ?_
        rw [norm_sub_rev]
    _ = ∫⁻ z in Metric.ball (0 : R3) (r + A + 1), ENNReal.ofReal (‖z‖⁻¹) :=
        Work.CoreResiduals.BiotSavart.lintegral_ball_sub_eq x (r + A + 1)
          (fun z => ENNReal.ofReal (‖z‖⁻¹))
    _ = ∫⁻ z in Metric.ball (0 : R3) (r + A + 1), ENNReal.ofReal (‖z‖ ^ (-1 : ℝ)) := by
        refine lintegral_congr fun z => ?_
        rw [Real.rpow_neg_one]
    _ = ENNReal.ofReal
          (4 * Real.pi * (r + A + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)) :=
        Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow (-1) (by norm_num)
          (r + A + 1) hρ

/-- The `ℝ≥0∞`-integral of `‖x - y‖⁻¹ 1_{K×L}` over `ℝ³ × ℝ³` is finite for compact `K`, `L`. -/
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
  have hA0 : 0 ≤ max rK 0 := le_max_right _ _
  have hB0 : 0 ≤ max rL 0 := le_max_right _ _
  have hKsub : K ⊆ Metric.closedBall (0 : R3) (max rK 0) := fun x hx =>
    Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp (hrK hx)) (le_max_left _ _))
  have hLsub : L ⊆ Metric.closedBall (0 : R3) (max rL 0) := fun x hx =>
    Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp (hrL hx)) (le_max_left _ _))
  have hinner_le : ∀ x : R3, ‖x‖ ≤ max rK 0 →
      ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
          ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y)
        ≤ ENNReal.ofReal
            (4 * Real.pi * (max rL 0 + max rK 0 + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)) := by
    intro x hx
    refine le_trans ?_ (lintegral_inv_norm_mul_indicator_ball_le x hB0 hx)
    refine lintegral_mono fun y => ?_
    simp only []
    by_cases hy : y ∈ L
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hLsub hy)]
    · rw [Set.indicator_of_notMem hy, ENNReal.ofReal_zero, mul_zero]
      exact bot_le
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
  have hmeas : Measurable (fun p : R3 × R3 => ENNReal.ofReal (‖p.1 - p.2‖⁻¹) *
        ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) p.1) *
        ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) p.2)) :=
    ((((continuous_fst.sub continuous_snd).norm.measurable.inv).ennreal_ofReal).mul
      ((measurable_const.indicator hKmeas).ennreal_ofReal.comp measurable_fst)).mul
      ((measurable_const.indicator hLmeas).ennreal_ofReal.comp measurable_snd)
  calc ∫⁻ p : R3 × R3, ENNReal.ofReal ((‖p.1 - p.2‖)⁻¹ *
        (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
      ∂(volume.prod volume)
      = ∫⁻ x : R3, ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) := by
        rw [lintegral_congr hpoint]
        exact lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ x : R3, ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x) *
          ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul' (ENNReal.ofReal ((K.indicator (fun _ => (1 : ℝ))) x)) _
          ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        ac_rfl
    _ = ∫⁻ x in K, ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y) := by
        rw [← lintegral_indicator hKmeas
          (fun x => ∫⁻ y : R3, ENNReal.ofReal (‖x - y‖⁻¹) *
            ENNReal.ofReal ((L.indicator (fun _ => (1 : ℝ))) y))]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ K
        · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_one, one_mul]
        · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero, zero_mul]
    _ ≤ ∫⁻ x in K, ENNReal.ofReal
          (4 * Real.pi * (max rL 0 + max rK 0 + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)) :=
        setLIntegral_mono measurable_const fun x hx =>
          hinner_le x (by simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hKsub hx))
    _ = ENNReal.ofReal
          (4 * Real.pi * (max rL 0 + max rK 0 + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)) * volume K := by
        rw [← lintegral_indicator hKmeas
          (fun _ => ENNReal.ofReal
            (4 * Real.pi * (max rL 0 + max rK 0 + 1) ^ ((-1 : ℝ) + 3) / ((-1 : ℝ) + 3)))]
        exact lintegral_indicator_const hKmeas _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- The joint integrability of the Newtonian kernel against a bounded compactly supported
measurable function. -/
private theorem integrable_prod_inv_norm_mul_joint {g : R3 × R3 → ℝ}
    (hgmeas : AEStronglyMeasurable g (volume.prod volume))
    {C : ℝ} {K L : Set R3} (hK : IsCompact K) (hL : IsCompact L)
    (hbdd : ∀ p, ‖g p‖ ≤ C) (hsupp : ∀ p, g p ≠ 0 → p.1 ∈ K ∧ p.2 ∈ L) :
    Integrable (fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ * g p) (volume.prod volume) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hLmeas : MeasurableSet L := hL.isClosed.measurableSet
  have hκ_int : Integrable (fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ *
      (K.indicator (fun _ => (1 : ℝ))) p.1 * (L.indicator (fun _ => (1 : ℝ))) p.2)
      (volume.prod volume) := by
    refine ⟨?_, ?_⟩
    · exact ((((continuous_fst.sub continuous_snd).norm.measurable.inv).mul
        ((measurable_const.indicator hKmeas).comp measurable_fst)).mul
        ((measurable_const.indicator hLmeas).comp measurable_snd)).aestronglyMeasurable
    · refine (MeasureTheory.hasFiniteIntegral_iff_ofReal
        (f := fun p : R3 × R3 => (‖p.1 - p.2‖)⁻¹ * (K.indicator (fun _ => (1 : ℝ))) p.1 *
          (L.indicator (fun _ => (1 : ℝ))) p.2) ?_).mpr
        (lintegral_prod_inv_norm_indicator_lt_top hK hL)
      exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  refine (hκ_int.bdd_mul hgmeas (Filter.Eventually.of_forall hbdd)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : g p = 0
  · simp only [hp, mul_zero, zero_mul]
  · obtain ⟨h1, h2⟩ := hsupp p hp
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    ring

/-- The Newtonian potential of a scalar test function, `y ↦ ∫ t, ‖y - t‖⁻¹ * k t`.  It is the
convolution of the test function `k` with the locally integrable kernel `‖·‖⁻¹`; its smoothness
(`∀ n, ContDiff ℝ n`) is what lets the weak divergence-free condition of `ω` be tested against it.
Kept private to this file (it is a bookkeeping device, not part of the area's vocabulary). -/
private def newtonPotentialScalar (k : R3 → ℝ) (y : R3) : ℝ := ∫ t, (‖y - t‖)⁻¹ * k t

theorem weakDivFree_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hω : Work.FTS.BSSwirl.WeakDivFree ω) :
    Work.FTS.BSSwirl.WeakDivFree (Work.FTS.BSSwirl.newtonPotential ω) := by
  intro k hk hc
  classical
  -- ## integrability of the shifted kernel on the support ball
  have hker : ∀ x : R3, IntegrableOn (fun y : R3 => (‖x - y‖)⁻¹)
      (Metric.closedBall 0 R) volume := by
    intro x
    have h1 : IntegrableOn (fun y : R3 => (‖y - x‖)⁻¹)
        (Metric.closedBall x (‖x‖ + R)) volume :=
      integrableOn_inv_norm_sub_closedBall x (‖x‖ + R)
    have hsub : Metric.closedBall (0 : R3) R ⊆ Metric.closedBall x (‖x‖ + R) := by
      intro y hy
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy ⊢
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
        _ ≤ R + ‖x‖ := by linarith
        _ = ‖x‖ + R := by ring
    refine (h1.mono_set hsub).congr_fun ?_ measurableSet_closedBall
    intro y _
    simp only [norm_sub_rev]
  have hker_r : ∀ r : ℝ, IntegrableOn (fun z : R3 => (‖z‖)⁻¹) (Metric.closedBall 0 r) volume := by
    intro r
    have h1 : IntegrableOn (fun z : R3 => (‖z - 0‖)⁻¹) (Metric.closedBall 0 r) volume :=
      integrableOn_inv_norm_sub_closedBall (0 : R3) r
    simpa using h1
  -- ## integrability of the Newtonian integrand
  have hInt : ∀ x : R3, Integrable (fun y : R3 => (‖x - y‖)⁻¹ • ω y) := by
    intro x
    have hb : IntegrableOn (fun y : R3 => (‖x - y‖)⁻¹ * M) (Metric.closedBall 0 R) volume :=
      (hker x).mul_const M
    refine Integrable.mono' (hb.integrable_indicator measurableSet_closedBall) ?_ ?_
    · have hscal : AEStronglyMeasurable (fun y : R3 => (‖x - y‖)⁻¹) volume :=
        ((continuous_const.sub continuous_id).norm.measurable.inv).aestronglyMeasurable
      exact hscal.smul hmeas
    · filter_upwards with y
      by_cases hy : y ∈ Metric.closedBall 0 R
      · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbdd y) (by positivity)
      · have h0 : ω y = 0 := by
          by_contra hne
          exact hy (hsupp y hne)
        rw [h0, smul_zero, norm_zero, Set.indicator_of_notMem hy]
  -- ## step 1: the inner product with the gradient, pointwise
  have hstep1 : ∀ x : R3, inner ℝ (newtonPotential ω x) (gradient k x)
      = (4 * Real.pi)⁻¹ * ∫ y, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y) := by
    intro x
    rw [newtonPotential_apply, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    congr 1
    rw [real_inner_comm]
    simp only [← innerSL_apply_apply]
    rw [← ContinuousLinearMap.integral_comp_comm (innerSL ℝ (gradient k x)) (hInt x)]
    apply integral_congr_ae
    filter_upwards with y
    rw [ContinuousLinearMap.map_smul, innerSL_apply_apply, smul_eq_mul, inner_gradient_left]
  have hstep2 : ∫ x, inner ℝ (newtonPotential ω x) (gradient k x)
      = (4 * Real.pi)⁻¹ * ∫ x, ∫ y, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y) := by
    rw [show (∫ x, inner ℝ (newtonPotential ω x) (gradient k x))
        = ∫ x, (4 * Real.pi)⁻¹ * (∫ y, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y)) from
      integral_congr_ae (Eventually.of_forall hstep1)]
    rw [MeasureTheory.integral_const_mul]
  -- ## joint integrability of the double integrand, and Fubini
  obtain ⟨C0, hC0⟩ := ((hk 1).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hc.fderiv ℝ)
  have hC0nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 0)
  have hgmeas : AEStronglyMeasurable (fun p : R3 × R3 => (fderiv ℝ k p.1) (ω p.2))
      (volume.prod volume) := by
    have hgradcont : Continuous (fun x : R3 => gradient k x) := by
      have h : Continuous fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ k x) :=
        (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
          ((hk 1).continuous_fderiv (by norm_num))
      simpa [gradient, Function.comp_def] using h
    have h1 : AEStronglyMeasurable (fun p : R3 × R3 => gradient k p.1) (volume.prod volume) :=
      (hgradcont.comp continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : R3 × R3 => ω p.2) (volume.prod volume) :=
      hmeas.comp_snd
    have h3 : AEStronglyMeasurable (fun p : R3 × R3 => inner ℝ (gradient k p.1) (ω p.2))
        (volume.prod volume) := h1.inner h2
    simpa only [inner_gradient_left] using h3
  have hbdd_g : ∀ p : R3 × R3, ‖(fderiv ℝ k p.1) (ω p.2)‖ ≤ C0 * M := by
    intro p
    calc ‖(fderiv ℝ k p.1) (ω p.2)‖ ≤ ‖fderiv ℝ k p.1‖ * ‖ω p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C0 * M := mul_le_mul (hC0 p.1) (hbdd p.2) (norm_nonneg _) hC0nn
  have hsupp_g : ∀ p : R3 × R3, (fderiv ℝ k p.1) (ω p.2) ≠ 0 →
      p.1 ∈ tsupport k ∧ p.2 ∈ Metric.closedBall 0 R := by
    intro p hp
    constructor
    · by_contra hx
      rw [notMem_tsupport_iff_eventuallyEq] at hx
      have hz : fderiv ℝ k p.1 = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq hx]
        simp
      rw [hz, zero_apply] at hp
      exact hp rfl
    · by_contra hy
      have h0 : ω p.2 = 0 := by
        by_contra hne
        exact hy (hsupp _ hne)
      rw [h0, map_zero] at hp
      exact hp rfl
  have hjoint : Integrable
      (Function.uncurry (fun x y : R3 => (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y)))
      (volume.prod volume) :=
    integrable_prod_inv_norm_mul_joint (g := fun p : R3 × R3 => (fderiv ℝ k p.1) (ω p.2)) hgmeas
      (C := C0 * M) (K := tsupport k) (L := Metric.closedBall 0 R) hc.isCompact
      (isCompact_closedBall 0 R) hbdd_g hsupp_g
  have hstep3 : ∫ x, ∫ y, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y)
      = ∫ y, ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y) :=
    integral_integral_swap hjoint
  -- ## step 2: for fixed `y`, the inner `x`-integral is the derivative of the Newtonian potential
  --    of the test function `k`, tested against `ω y`
  have hstep4 : ∀ y : R3, ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y)
      = (fderiv ℝ (newtonPotentialScalar k) y) (ω y) := by
    intro y
    exact (convolution_inv_norm_fderiv (hk 1) hc y (ω y)).symm
  -- ## the Newtonian potential of the test function is smooth
  have hMk : LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball 0
    exact (hker_r r).mono_set (fun z hz => Metric.mem_closedBall.mpr (le_of_lt (hr hz)))
  have hGsmooth : ∀ n : ℕ, ContDiff ℝ n (newtonPotentialScalar k) := by
    intro n
    have hconv : ContDiff ℝ (n : WithTop ℕ∞)
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun z : R3 => (‖z‖)⁻¹)) := by
      have h := hc.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (n := (n : ℕ∞)) (hk n) hMk
      simpa using h
    have heq : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun z : R3 => (‖z‖)⁻¹))
        = newtonPotentialScalar k := by
      funext y
      rw [MeasureTheory.convolution_lsmul]
      apply integral_congr_ae
      filter_upwards with t
      rw [smul_eq_mul, mul_comm]
    rwa [heq] at hconv
  -- ## step 3: the weak divergence-free condition kills the pairing
  let χ : R3 → ℝ := fun y => Real.smoothTransition ((R + 1) ^ 2 + 1 - ‖y‖ ^ 2)
  have hχsm : ∀ n : ℕ, ContDiff ℝ n χ := by
    intro n
    have hst : ContDiff ℝ (n : WithTop ℕ∞) Real.smoothTransition := by
      simpa using (Real.smoothTransition.contDiff (n := (n : ℕ∞)))
    have harg : ContDiff ℝ (n : WithTop ℕ∞) (fun y : R3 => (R + 1) ^ 2 + 1 - ‖y‖ ^ 2) :=
      contDiff_const.sub (contDiff_norm_sq ℝ)
    exact hst.comp harg
  have hχone : ∀ y ∈ Metric.closedBall 0 R, χ y = 1 := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    have h1 : 1 ≤ (R + 1) ^ 2 + 1 - ‖y‖ ^ 2 := by
      nlinarith [hR, norm_nonneg y, hy, sq_nonneg (R + 1), sq_nonneg (R - ‖y‖)]
    exact Real.smoothTransition.one_of_one_le h1
  have hχev : ∀ y ∈ Metric.closedBall 0 R, χ =ᶠ[𝓝 y] 1 := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1)] with z hz
    simp only [Metric.mem_ball, dist_eq_norm] at hz
    have hz1 : ‖z‖ ≤ R + 1 := by
      have hle := norm_add_le (z - y) y
      rw [sub_add_cancel] at hle
      linarith
    have h1 : 1 ≤ (R + 1) ^ 2 + 1 - ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z, hz1, hR, sq_nonneg (R + 1), sq_nonneg (R + 1 - ‖z‖)]
    exact Real.smoothTransition.one_of_one_le h1
  have hχcs : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall 0 (Real.sqrt ((R + 1) ^ 2 + 1)))
      (isCompact_closedBall 0 (Real.sqrt ((R + 1) ^ 2 + 1))) ?_
    intro y hy
    rw [Function.mem_support] at hy
    simp only [χ] at hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hpos : 0 < (R + 1) ^ 2 + 1 - ‖y‖ ^ 2 := by
      by_contra hle
      rw [not_lt] at hle
      rw [Real.smoothTransition.zero_of_nonpos hle] at hy
      exact hy rfl
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hstep5 : ∫ y, (fderiv ℝ (newtonPotentialScalar k) y) (ω y) = 0 := by
    have hpt1 : ∀ y : R3, (fderiv ℝ (newtonPotentialScalar k) y) (ω y)
        = (fderiv ℝ (χ * newtonPotentialScalar k) y) (ω y) := by
      intro y
      by_cases hy : ω y = 0
      · rw [hy, map_zero, map_zero]
      · have hyb : y ∈ Metric.closedBall 0 R := hsupp y hy
        have heq : (χ * newtonPotentialScalar k) =ᶠ[𝓝 y] newtonPotentialScalar k := by
          filter_upwards [hχev y hyb] with z hz
          simp only [Pi.mul_apply, hz, Pi.one_apply, one_mul]
        rw [Filter.EventuallyEq.fderiv_eq heq]
    have hpt2 : ∀ y : R3, (fderiv ℝ (χ * newtonPotentialScalar k) y) (ω y)
        = inner ℝ (ω y) (gradient (χ * newtonPotentialScalar k) y) := by
      intro y
      rw [real_inner_comm, inner_gradient_left]
    rw [show (∫ y, (fderiv ℝ (newtonPotentialScalar k) y) (ω y))
        = ∫ y, (fderiv ℝ (χ * newtonPotentialScalar k) y) (ω y) from
      integral_congr_ae (Eventually.of_forall hpt1)]
    rw [show (∫ y, (fderiv ℝ (χ * newtonPotentialScalar k) y) (ω y))
        = ∫ y, inner ℝ (ω y) (gradient (χ * newtonPotentialScalar k) y) from
      integral_congr_ae (Eventually.of_forall hpt2)]
    exact hω (χ * newtonPotentialScalar k) (fun n => (hχsm n).mul (hGsmooth n))
      hχcs.mul_right
  -- ## assembly
  have hfinal : ∫ x, inner ℝ (newtonPotential ω x) (gradient k x) = 0 := by
    rw [hstep2, hstep3]
    rw [show (∫ y, ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) (ω y))
        = ∫ y, (fderiv ℝ (newtonPotentialScalar k) y) (ω y) from
      integral_congr_ae (Eventually.of_forall fun y => hstep4 y)]
    rw [hstep5, mul_zero]
  exact hfinal

end

end Work.FTS.BSSwirl
