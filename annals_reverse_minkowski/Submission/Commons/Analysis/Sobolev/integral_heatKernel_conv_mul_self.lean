import Mathlib
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq

open MeasureTheory Filter Function
open scoped Topology RealInnerProductSpace BigOperators

namespace Commons.Analysis.Sobolev

set_option maxHeartbeats 1000000

/-- A locally integrable function with compact support on a finite-dimensional real vector space
is integrable. -/
lemma integrable_of_locallyIntegrable_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : LocallyIntegrable f volume) (hfc : HasCompactSupport f) :
    Integrable f volume := by
  have hmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have h_eq : f = (tsupport f).indicator f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact image_eq_zero_of_notMem_tsupport hx
  rw [h_eq, integrable_indicator_iff hmeas]
  exact hf.integrableOn_isCompact hfc.isCompact

/-- Integrability of `(x,t) ↦ K t * G x * Ψ (x+t)` on the product, for `K, G` integrable and `Ψ`
bounded and continuous. -/
lemma integrable_mul_mul_add_of_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K G Ψ : E → ℝ) (hK : Integrable K) (hG : Integrable G) (hΨcont : Continuous Ψ)
    {C : ℝ} (hC : ∀ x, |Ψ x| ≤ C) :
    Integrable (fun p : E × E => K p.2 * G p.1 * Ψ (p.1 + p.2)) (volume.prod volume) := by
  have haes : AEStronglyMeasurable (fun p : E × E => K p.2 * G p.1 * Ψ (p.1 + p.2))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : E × E => K p.2) (volume.prod volume) :=
      hK.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEStronglyMeasurable (fun p : E × E => G p.1) (volume.prod volume) :=
      hG.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h3 : AEStronglyMeasurable (fun p : E × E => Ψ (p.1 + p.2)) (volume.prod volume) :=
      (hΨcont.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  have hdom : Integrable (fun p : E × E => C * (‖G p.1‖ * ‖K p.2‖)) (volume.prod volume) :=
    (hG.norm.mul_prod hK.norm).const_mul C
  refine Integrable.mono' hdom haes ?_
  filter_upwards with p
  have hb : ‖K p.2‖ * ‖G p.1‖ * |Ψ (p.1 + p.2)| ≤ C * (‖G p.1‖ * ‖K p.2‖) := by
    have h1 : ‖K p.2‖ * ‖G p.1‖ * |Ψ (p.1 + p.2)| ≤ ‖K p.2‖ * ‖G p.1‖ * C := by
      have h2 : (0 : ℝ) ≤ ‖K p.2‖ * ‖G p.1‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith [hC (p.1 + p.2), abs_nonneg (Ψ (p.1 + p.2))]
    have h3 : ‖K p.2‖ * ‖G p.1‖ * C = C * (‖G p.1‖ * ‖K p.2‖) := by ring
    linarith [h1, h3.le, h3.ge]
  rw [norm_mul, norm_mul, Real.norm_eq_abs]
  exact hb

/-- Integrability of `(x,t) ↦ K t * G (x-t) * Ψ x` on the product, for `K, G` integrable and `Ψ`
bounded and continuous. -/
lemma integrable_mul_shift_mul_of_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K G Ψ : E → ℝ) (hK : Integrable K) (hG : Integrable G) (hΨcont : Continuous Ψ)
    {C : ℝ} (hC : ∀ x, |Ψ x| ≤ C) :
    Integrable (fun p : E × E => K p.2 * G (p.1 - p.2) * Ψ p.1) (volume.prod volume) := by
  have hT : MeasurePreserving (fun z : E × E => (z.1 - z.2, z.2)) (volume.prod volume)
      (volume.prod volume) := measurePreserving_sub_prod volume volume
  have hF0 : Integrable (fun p : E × E => K p.2 * G p.1 * Ψ (p.1 + p.2)) (volume.prod volume) :=
    integrable_mul_mul_add_of_integrable K G Ψ hK hG hΨcont hC
  have haes : AEStronglyMeasurable (fun p : E × E => K p.2 * G p.1 * Ψ (p.1 + p.2))
      (volume.prod volume) := hF0.aestronglyMeasurable
  have hcomp : Integrable (fun p : E × E => K p.2 * G (p.1 - p.2) * Ψ ((p.1 - p.2) + p.2))
      (volume.prod volume) := (hT.integrable_comp haes).mpr hF0
  refine hcomp.congr ?_
  filter_upwards with p
  rw [sub_add_cancel]

/-- **Self-adjointness of convolution with an even integrable kernel.**
For an integrable even kernel `K`, an integrable `G` and a continuous bounded `Ψ`,
`∫ (K ⋆ G) Ψ = ∫ G (K ⋆ Ψ)`. -/
theorem integral_convolution_selfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K G Ψ : E → ℝ) (hK : Integrable K) (hKsym : ∀ x, K (-x) = K x) (hG : Integrable G)
    (hΨcont : Continuous Ψ) {C : ℝ} (hC : ∀ x, |Ψ x| ≤ C) :
    (∫ x, (∫ y, K (x - y) * G y) * Ψ x)
      = ∫ x, G x * (∫ y, K (x - y) * Ψ y) := by
  set F : E × E → ℝ := fun p => K p.2 * G (p.1 - p.2) * Ψ p.1 with hFdef
  set F₀ : E × E → ℝ := fun p => K p.2 * G p.1 * Ψ (p.1 + p.2) with hF0def
  have hF0int : Integrable F₀ (volume.prod volume) :=
    integrable_mul_mul_add_of_integrable K G Ψ hK hG hΨcont hC
  have hF0aes : AEStronglyMeasurable F₀ (volume.prod volume) := hF0int.aestronglyMeasurable
  have hFint : Integrable F (volume.prod volume) :=
    integrable_mul_shift_mul_of_integrable K G Ψ hK hG hΨcont hC
  have hT : MeasurePreserving (fun z : E × E => (z.1 - z.2, z.2)) (volume.prod volume)
      (volume.prod volume) := measurePreserving_sub_prod volume volume
  have hconv : ∀ x, (∫ y, K (x - y) * G y) = ∫ t, K t * G (x - t) := by
    intro x
    have h : (fun y => K (x - y) * G y) = (fun y => (fun t => K t * G (x - t)) (x - y)) := by
      funext y; simp only [sub_sub_cancel]
    rw [h]
    exact MeasureTheory.integral_sub_left_eq_self (fun t => K t * G (x - t)) volume x
  have hconv' : ∀ x, (∫ y, K (x - y) * Ψ y) = ∫ t, K t * Ψ (x - t) := by
    intro x
    have h : (fun y => K (x - y) * Ψ y) = (fun y => (fun t => K t * Ψ (x - t)) (x - y)) := by
      funext y; simp only [sub_sub_cancel]
    rw [h]
    exact MeasureTheory.integral_sub_left_eq_self (fun t => K t * Ψ (x - t)) volume x
  have step1 : (∫ x, (∫ y, K (x - y) * G y) * Ψ x) = ∫ z, F z ∂(volume.prod volume) := by
    rw [show (fun x => (∫ y, K (x - y) * G y) * Ψ x)
          = (fun x => (∫ t, K t * G (x - t)) * Ψ x) from by
        funext x; rw [hconv x]]
    rw [show (fun x => (∫ t, K t * G (x - t)) * Ψ x)
          = (fun x => ∫ t, (K t * G (x - t)) * Ψ x) from by
        funext x; exact (MeasureTheory.integral_mul_const (Ψ x) (fun t => K t * G (x - t))).symm]
    exact (integral_prod F hFint).symm
  have step2 : (∫ z, F z ∂(volume.prod volume)) = ∫ z, F₀ z ∂(volume.prod volume) := by
    have hpt : F = fun z : E × E => F₀ (z.1 - z.2, z.2) := by
      funext z; simp only [hFdef, hF0def, sub_add_cancel]
    rw [hpt]
    conv_rhs => rw [← hT.map_eq]
    exact (MeasureTheory.integral_map hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hF0aes)).symm
  have step3 : (∫ z, F₀ z ∂(volume.prod volume)) = ∫ x, G x * (∫ t, K t * Ψ (x - t)) := by
    rw [integral_prod F₀ hF0int]
    apply integral_congr_ae
    filter_upwards with x
    have h1 : (∫ y, F₀ (x, y)) = ∫ y, K y * G x * Ψ (x + y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [hF0def]
    rw [h1]
    have h2 : (∫ y, K y * G x * Ψ (x + y)) = ∫ y, K y * G x * Ψ (x - y) := by
      rw [← MeasureTheory.integral_neg_eq_self (fun y => K y * G x * Ψ (x - y)) volume]
      apply integral_congr_ae
      filter_upwards with y
      rw [hKsym y, sub_neg_eq_add]
    rw [h2]
    rw [← MeasureTheory.integral_const_mul (G x) (fun y => K y * Ψ (x - y))]
    apply integral_congr_ae
    filter_upwards with y
    ring
  have hRHS : (∫ x, G x * (∫ y, K (x - y) * Ψ y))
      = ∫ x, G x * (∫ t, K t * Ψ (x - t)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hconv' x]
  calc (∫ x, (∫ y, K (x - y) * G y) * Ψ x)
      = ∫ z, F z ∂(volume.prod volume) := step1
    _ = ∫ z, F₀ z ∂(volume.prod volume) := step2
    _ = ∫ x, G x * (∫ t, K t * Ψ (x - t)) := step3
    _ = ∫ x, G x * (∫ y, K (x - y) * Ψ y) := hRHS.symm

/-- Integrability of the Gaussian heat kernel. -/
lemma integrable_heatKernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : E =>
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))))
      volume := by
  have ht4 : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hbase : Integrable (fun z : E => Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2)) volume := by
    have h := Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (V := E) (1 / (4 * t)) ht4 0
    simpa using h
  have h2 := hbase.const_mul ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2))
  refine h2.congr ?_
  filter_upwards with z
  have hexp : -(1 / (4 * t)) * ‖z‖ ^ 2 = -(‖z‖ ^ 2 / (4 * t)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [hexp]

theorem integral_heatKernel_conv_mul_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (t : ℝ) (ht : 0 < t) (G Ψ : E → ℝ) (hG : MeasureTheory.LocallyIntegrable G MeasureTheory.volume)
    (hGc : HasCompactSupport G) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    (∫ x, (∫ y, (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x - y‖ ^ 2 / (4 * t))) * G y) * Ψ x)
      = ∫ x, G x * (∫ y, (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x - y‖ ^ 2 / (4 * t))) * Ψ y) := by
  have hKint : Integrable (fun z : E =>
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))))
      volume := integrable_heatKernel t ht
  have hKsym : ∀ x, (fun z : E =>
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) (-x)
      = (fun z : E => (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
          * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) x := by
    intro x; simp only [norm_neg]
  have hGint : Integrable G volume := integrable_of_locallyIntegrable_hasCompactSupport hG hGc
  have hΨcont : Continuous Ψ := hΨ.continuous
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, |Ψ x| ≤ C := by
    have hbdd := hΨ.continuous.abs.bddAbove_range_of_hasCompactSupport hΨc.abs
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  exact integral_convolution_selfAdjoint (fun z : E =>
    (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))))
    G Ψ hKint hKsym hGint hΨcont hC

end Commons.Analysis.Sobolev
