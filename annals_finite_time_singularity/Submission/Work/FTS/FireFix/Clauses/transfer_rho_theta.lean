import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.Clauses.XferChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.FTS.FireFix.Clauses

theorem transfer_rho_theta {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {F : ℝ → ℝ → ℝ}
    (hF : ∀ z θ, 0 ≤ F z θ)
    (hint : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => F q.1 q.2 * q.1 ^ (1 / α - 1) * Real.cos q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        F (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), F (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x))
        = 2 * Real.pi * B ^ (1 / α) / (3 * α) *
          ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
            F q.1 q.2 * q.1 ^ (1 / α - 1) * Real.cos q.2 := by
  have hVmeas : MeasurableSet Adom := measurableSet_Ioi.prod measurableSet_Ioo
  set c : ℝ := 2 * Real.pi * B ^ (1 / α) / (3 * α) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set w : ℝ × ℝ → ℝ := fun q => q.1 ^ (1 / α - 1) * Real.cos q.2 with hwdef
  set T : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ :=
    fun x => (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x) with hTdef
  have hT : Measurable T := measurable_rhoTheta hα.le
  -- (1) the hypothesis restated with the angular weight `w`
  have hintW : Integrable (fun q : ℝ × ℝ => F q.1 q.2 * w q) (volume.restrict Adom) := by
    refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hwdef]
    ring
  -- (2) the angular weight does not vanish on the domain
  have hwne : ∀ q ∈ Adom, w q ≠ 0 := by
    rintro ⟨r, θ⟩ hq
    obtain ⟨hr, hθ⟩ := hq
    simp only [hwdef]
    exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hr (1 / α - 1)))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo hθ))
  -- (3) the angular weight is nonnegative on the domain
  have hwnonneg : ∀ q ∈ Adom, 0 ≤ w q := by
    rintro ⟨r, θ⟩ hq
    obtain ⟨hr, hθ⟩ := hq
    simp only [hwdef]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hr (1 / α - 1)))
      (le_of_lt (Real.cos_pos_of_mem_Ioo hθ))
  -- (4) a.e.-measurability of the angular weight
  have hw_aemeas : AEMeasurable w (volume.restrict Adom) := by
    have hs : MeasurableSet {q : ℝ × ℝ | 0 < q.1} := measurableSet_Ioi.preimage measurable_fst
    have hcon : ContinuousOn (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1)) {q : ℝ × ℝ | 0 < q.1} :=
      continuous_fst.continuousOn.rpow_const (fun q hq => Or.inl (ne_of_gt hq))
    have h1 : AEMeasurable (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1))
        ((volume.restrict Adom).restrict {q : ℝ × ℝ | 0 < q.1}) := hcon.aemeasurable hs
    have heq : (volume.restrict Adom).restrict {q : ℝ × ℝ | 0 < q.1} = volume.restrict Adom := by
      rw [Measure.restrict_restrict (μ := (volume : Measure (ℝ × ℝ))) hs,
        Set.inter_eq_right.mpr (fun q hq => hq.1)]
    rw [heq] at h1
    exact h1.mul (Real.continuous_cos.measurable.comp measurable_snd).aemeasurable
  -- (5) a.e.-measurability of `F` on the domain, and a measurable version `F'` of it
  have hFae : AEMeasurable (fun q : ℝ × ℝ => F q.1 q.2) (volume.restrict Adom) := by
    have h1 : AEMeasurable (fun q : ℝ × ℝ => F q.1 q.2 * w q) (volume.restrict Adom) :=
      hintW.aestronglyMeasurable.aemeasurable
    refine (h1.div hw_aemeas).congr ?_
    filter_upwards [self_mem_ae_restrict hVmeas] with q hq
    show (F q.1 q.2 * w q) / w q = F q.1 q.2
    rw [mul_div_cancel_right₀ _ (hwne q hq)]
  obtain ⟨F', hF'meas, hF'ae⟩ := hFae
  -- (6) the change of variables, in the pair form
  have htrans : ∀ G : ℝ × ℝ → ENNReal, Measurable G →
      (∫⁻ x : EuclideanSpace ℝ (Fin 3), G (T x))
        = ENNReal.ofReal c * ∫⁻ q in Adom, ENNReal.ofReal (w q) * G q := by
    intro G hG
    have h := lintegral_transfer (α := α) (B := B) hα hB (g := fun z θ => G (z, θ))
      (show Measurable (fun q : ℝ × ℝ => G (q.1, q.2)) from hG)
    simpa only [hTdef, hcdef] using h
  -- (7) the pushforward of Lebesgue by `T` vanishes on the domains where `F` vanishes a.e.
  have hac : ∀ S : Set (ℝ × ℝ), MeasurableSet S → (volume.restrict Adom) S = 0 →
      (Measure.map T volume) S = 0 := by
    intro S hSmeas hS0
    have h := htrans (S.indicator fun _ => (1 : ENNReal)) (Measurable.indicator measurable_const hSmeas)
    have hL : (∫⁻ x : EuclideanSpace ℝ (Fin 3), S.indicator (fun _ => (1 : ENNReal)) (T x))
        = (Measure.map T volume) S := by
      rw [← lintegral_indicator_one (μ := Measure.map T volume) hSmeas]
      exact (lintegral_map (measurable_const.indicator hSmeas) hT).symm
    have hR : (∫⁻ q in Adom, ENNReal.ofReal (w q) * S.indicator (fun _ => (1 : ENNReal)) q) = 0 := by
      have h1 : (fun q : ℝ × ℝ => ENNReal.ofReal (w q) * S.indicator (fun _ => (1 : ENNReal)) q)
          = S.indicator (fun q => ENNReal.ofReal (w q)) := by
        funext q
        by_cases hq : q ∈ S
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, mul_one]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
      rw [h1, lintegral_indicator hSmeas]
      exact setLIntegral_measure_zero S _ hS0
    rw [← hL, h, hR, mul_zero]
  -- (8) the exceptional set is null
  have hnull : volume {x : EuclideanSpace ℝ (Fin 3) | F (T x).1 (T x).2 ≠ F' (T x)} = 0 := by
    have hN : (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q} = 0 := hF'ae
    have hN' : (volume.restrict Adom)
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) = 0 := by
      rw [measure_toMeasurable]; exact hN
    have hmeasN' : MeasurableSet
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
      measurableSet_toMeasurable _ _
    have h0 : (Measure.map T volume)
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) = 0 :=
      hac _ hmeasN' hN'
    refine le_antisymm ?_ zero_le
    calc volume {x : EuclideanSpace ℝ (Fin 3) | F (T x).1 (T x).2 ≠ F' (T x)}
        ≤ volume (T ⁻¹' toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
          measure_mono fun x hx => subset_toMeasurable _ _ hx
      _ = (Measure.map T volume)
            (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
          (Measure.map_apply hT hmeasN').symm
      _ = 0 := h0
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin 3) ∂volume, F (T x).1 (T x).2 = F' (T x) :=
    (MeasureTheory.ae_iff).mpr hnull
  -- (9) a.e.-strong measurability of `F ∘ T`
  have hFT_aesm : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => F (T x).1 (T x).2) volume := by
    refine ((hF'meas.comp hT).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with x hx
    exact hx.symm
  -- (10) the two lintegral identities
  have hgeJ : 0 ≤ᵐ[volume.restrict Adom] (fun q : ℝ × ℝ => F q.1 q.2 * w q) := by
    filter_upwards [self_mem_ae_restrict hVmeas] with q hq
    exact mul_nonneg (hF q.1 q.2) (hwnonneg q hq)
  have hkey : (∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F q.1 q.2))
      = ENNReal.ofReal (∫ q in Adom, F q.1 q.2 * w q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintW hgeJ]
    refine setLIntegral_congr_fun hVmeas fun q _ => ?_
    rw [mul_comm, ← ENNReal.ofReal_mul (hF q.1 q.2)]
  have hmain : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F' (T x)))
      = ENNReal.ofReal c * ENNReal.ofReal (∫ q in Adom, F q.1 q.2 * w q) := by
    have h1 := htrans (fun q => ENNReal.ofReal (F' q)) (ENNReal.measurable_ofReal.comp hF'meas)
    have h2 : (∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F' q))
        = ∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F q.1 q.2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF'ae] with q hq
      rw [← hq]
    rw [h1, h2, hkey]
  have hIntEq : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F (T x).1 (T x).2))
      = ∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F' (T x)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  -- (11) integrability
  have hnorm : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ‖F (T x).1 (T x).2‖ₑ)
      = ∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F (T x).1 (T x).2) :=
    lintegral_congr fun x => Real.enorm_of_nonneg (hF (T x).1 (T x).2)
  refine ⟨⟨hFT_aesm, ?_⟩, ?_⟩
  · show (∫⁻ x : EuclideanSpace ℝ (Fin 3), ‖F (T x).1 (T x).2‖ₑ) < ∞
    rw [hnorm, hIntEq, hmain, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => hF _ _) hFT_aesm,
      hIntEq, hmain, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hgeJ), hcdef]
    congr 1
    refine setIntegral_congr_fun hVmeas fun q _ => ?_
    simp only [hwdef]
    ring

end Work.FTS.FireFix.Clauses
