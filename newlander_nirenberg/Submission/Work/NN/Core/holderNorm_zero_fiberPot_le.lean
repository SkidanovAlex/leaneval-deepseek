/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The order-zero Schauder estimate for the fixed-disc Cauchy potential

`Work.NN.Core.fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w)/(w - z j) dw`
is the fixed-disc potential in the `j`-th fibre.  This file proves the order-zero estimate

  `‖fiberPot R j u‖_{C^{0,α}(polydisc 0 r)} ≤ C ‖u‖_{C^{0,α}(fiberAccess r j R)}`

for data supported in the band `‖z j‖ < R` (no bound on the transverse support), where
`fiberAccess r j R = polydisc 0 (Function.update r j R)` is the polydisc actually read by the
potential.  The proof splits the difference of the potential at `z, z'` into a fibre difference
(bounded by the two-pole kernel estimate `Work.NN.Core.twoPoleKernel_integral_mul_le`) and a
transverse difference (bounded by the `α`-seminorm of the data on the accessed polydisc).
-/
import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball
import Submission.Work.NN.Core.twoPoleKernel_integral_mul_le

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-! ## order-zero Hölder norm facts for a general real normed space -/

lemma holderNorm_zero_eq' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α f Ω
      = Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω := by
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

lemma norm_iteratedFDerivWithin_zero_sub' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply,
      iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y) (0 : Fin 0 → X)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDerivWithin_zero_apply] at h
    rw [show (∏ i : Fin 0, ‖(0 : Fin 0 → X) i‖) = 1 from by simp, mul_one] at h
    exact h

/-! ## the accessed polydisc -/

lemma update_mem_fiberAccess {n : ℕ} {r : Fin n → ℝ} {j : Fin n} {R : ℝ} {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) {w : ℂ} (hw : w ∈ Metric.ball 0 R) :
    Function.update z j w ∈ fiberAccess r j R := by
  rw [mem_fiberAccess]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Function.update_of_ne hi]; simpa using hz i
  · rw [Function.update_self]; simpa using hw

/-! ## one-pole integral bound -/

lemma integral_inv_sub_ball_le {R r0 : ℝ} (hR : 0 < R) (hr0 : 0 ≤ r0) (hr0R : r0 < R) :
    ∀ a : ℂ, ‖a‖ ≤ r0 → ∫ w in Metric.ball (0:ℂ) R, (‖w - a‖)⁻¹ ≤ 2 * Real.pi * (R + r0) := by
  intro a ha
  have hmp : MeasurePreserving (fun u : ℂ => a + u) volume volume :=
    MeasureTheory.measurePreserving_add_left volume a
  have hemb : MeasurableEmbedding (fun u : ℂ => a + u) := (MeasurableEquiv.addLeft a).measurableEmbedding
  have hpre : (fun u : ℂ => a + u) ⁻¹' Metric.ball (0:ℂ) R = Metric.ball (-a) R := by
    ext u
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [show a + u = u - (-a) from by ring]
  have hcv : ∫ w in Metric.ball (0:ℂ) R, (‖w - a‖)⁻¹
      = ∫ u in Metric.ball (-a) R, (‖u‖)⁻¹ := by
    rw [← MeasureTheory.MeasurePreserving.setIntegral_preimage_emb hmp hemb
      (fun w : ℂ => (‖w - a‖)⁻¹) (Metric.ball (0:ℂ) R), hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun u _ => ?_)
    rw [show a + u - a = u from by ring]
  have hsub : Metric.ball (-a) R ⊆ Metric.ball (0:ℂ) (R + r0) := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
    rw [sub_zero]
    calc ‖u‖ = ‖(u - (-a)) - a‖ := by ring_nf
      _ ≤ ‖u - (-a)‖ + ‖a‖ := norm_sub_le _ _
      _ < R + r0 := by linarith [ha]
  have hInt : IntegrableOn (fun u : ℂ => (‖u‖)⁻¹) (Metric.ball (0:ℂ) (R + r0)) := by
    simpa only [Real.rpow_neg_one]
      using (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := R + r0) (s := (-1:ℝ)) (by norm_num))
  calc ∫ w in Metric.ball (0:ℂ) R, (‖w - a‖)⁻¹
      = ∫ u in Metric.ball (-a) R, (‖u‖)⁻¹ := hcv
    _ ≤ ∫ u in Metric.ball (0:ℂ) (R + r0), (‖u‖)⁻¹ :=
        setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun w => by positivity)) hsub.eventuallyLE
    _ = 2 * Real.pi * (R + r0) := by
        rw [show (fun u : ℂ => (‖u‖)⁻¹) = (fun u : ℂ => ‖u‖ ^ (-1:ℝ)) from by
          funext u; rw [Real.rpow_neg_one]]
        rw [Work.CR.Flat.Cauchy.integral_norm_rpow_ball (by linarith) (by norm_num : (-2:ℝ) < -1)]
        rw [show (-1:ℝ) + 2 = 1 by norm_num, Real.rpow_one, div_one]

/-! ## two-pole integrand integrability (used to apply the pointwise domination) -/

lemma integrableOn_inv_mul_inv_ball {R : ℝ} {a b : ℂ} (hab : a ≠ b) :
    IntegrableOn (fun w : ℂ => (‖w - a‖ * ‖w - b‖)⁻¹) (Metric.ball 0 R) := by
  have h1 : Integrable (fun w : ℂ => (‖w - a‖)⁻¹) (volume.restrict (Metric.ball 0 R)) := by
    have h := (integrableOn_sub_inv_ball R a).norm
    simpa only [norm_inv] using h
  have h2 : Integrable (fun w : ℂ => (‖w - b‖)⁻¹) (volume.restrict (Metric.ball 0 R)) := by
    have h := (integrableOn_sub_inv_ball R b).norm
    simpa only [norm_inv] using h
  have hmaj : Integrable (fun w : ℂ => ‖a - b‖⁻¹ * ((‖w - a‖)⁻¹ + (‖w - b‖)⁻¹))
      (volume.restrict (Metric.ball 0 R)) := (h1.add h2).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact (by measurability : Measurable (fun w : ℂ => (‖w - a‖ * ‖w - b‖)⁻¹)).aestronglyMeasurable
  · filter_upwards with w
    show ‖(‖w - a‖ * ‖w - b‖)⁻¹‖ ≤ ‖a - b‖⁻¹ * ((‖w - a‖)⁻¹ + (‖w - b‖)⁻¹)
    rw [Real.norm_of_nonneg (by positivity)]
    rcases eq_or_lt_of_le (norm_nonneg (w - a)) with hp0 | hp'
    · rw [← hp0]; simp only [zero_mul, inv_zero]; positivity
    rcases eq_or_lt_of_le (norm_nonneg (w - b)) with hq0 | hq'
    · rw [← hq0]; simp only [mul_zero, inv_zero]; positivity
    have hδle : ‖a - b‖ ≤ ‖w - a‖ + ‖w - b‖ := by
      calc ‖a - b‖ = ‖(a - w) + (w - b)‖ := by ring_nf
        _ ≤ ‖a - w‖ + ‖w - b‖ := norm_add_le _ _
        _ = ‖w - a‖ + ‖w - b‖ := by rw [norm_sub_rev]
    rw [show (‖w - a‖ * ‖w - b‖)⁻¹ = 1/(‖w - a‖ * ‖w - b‖) by rw [one_div]]
    rw [show ‖a - b‖⁻¹ * ((‖w - a‖)⁻¹ + (‖w - b‖)⁻¹)
        = (‖w - a‖ + ‖w - b‖)/(‖a - b‖ * (‖w - a‖ * ‖w - b‖)) by
      field_simp
      ring]
    have hδpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖w - a‖ * ‖w - b‖)]
    have hsimpl : (‖w - a‖ + ‖w - b‖) / (‖a - b‖ * (‖w - a‖ * ‖w - b‖))
        * (‖w - a‖ * ‖w - b‖) = (‖w - a‖ + ‖w - b‖) / ‖a - b‖ := by
      field_simp
    rw [hsimpl, le_div_iff₀ hδpos]
    linarith

/-! ## fibre estimates for the fixed-disc potential -/

lemma norm_update_sub_update_le {n : ℕ} (z z' : Cn n) (j : Fin n) (w : ℂ) :
    ‖Function.update z j w - Function.update z' j w‖ ≤ ‖z - z'‖ := by
  have heq : Function.update z j w - Function.update z' j w = Function.update (z - z') j 0 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi, Pi.sub_apply]
  rw [heq]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  by_cases hi : i = j
  · subst hi; simp
  · rw [Function.update_of_ne hi]; exact norm_le_pi_norm (z - z') i

lemma norm_fiberPot_le {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {r : Fin n → ℝ}
    (hrj0 : 0 < r j) (hrjR : r j < R) {v : Cn n → ℂ} (hv : Continuous v)
    {A0 : ℝ} (hA0nn : 0 ≤ A0) (hA0 : ∀ x ∈ fiberAccess r j R, ‖v x‖ ≤ A0)
    {z : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    ‖fiberPot R j v z‖ ≤ 4 * R * A0 := by
  have hInt2 : Integrable (fun w : ℂ => (‖w - z j‖)⁻¹) (volume.restrict (Metric.ball 0 R)) := by
    have h := (integrableOn_sub_inv_ball R (z j)).norm
    simpa only [norm_inv] using h
  have hmaj : Integrable (fun w : ℂ => A0 * (‖w - z j‖)⁻¹) (volume.restrict (Metric.ball 0 R)) :=
    hInt2.const_mul A0
  have hpt : ∀ᵐ w ∂(volume.restrict (Metric.ball 0 R)),
      ‖v (Function.update z j w) / (w - z j)‖ ≤ A0 * (‖w - z j‖)⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hA0 _ (update_mem_fiberAccess hz hw)) (by positivity)
  have hzj : ‖z j‖ ≤ r j := le_of_lt (by simpa using hz j)
  have hkey : (∫ w in Metric.ball 0 R, A0 * (‖w - z j‖)⁻¹)
      ≤ A0 * (2 * Real.pi * (R + r j)) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_inv_sub_ball_le hR (le_of_lt hrj0) hrjR (z j) hzj) hA0nn
  have hpi : Real.pi⁻¹ * (2 * Real.pi) = 2 := by
    rw [mul_comm (2:ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  calc ‖fiberPot R j v z‖
      = Real.pi⁻¹ * ‖∫ w in Metric.ball 0 R, v (Function.update z j w) / (w - z j)‖ := by
        rw [fiberPot_apply, norm_mul, norm_neg, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]
    _ ≤ Real.pi⁻¹ * ∫ w in Metric.ball 0 R, A0 * (‖w - z j‖)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact norm_integral_le_of_norm_le hmaj hpt
    _ ≤ Real.pi⁻¹ * (A0 * (2 * Real.pi * (R + r j))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = A0 * (R + r j) * (Real.pi⁻¹ * (2 * Real.pi)) := by ring
    _ = A0 * (R + r j) * 2 := by rw [hpi]
    _ ≤ 4 * R * A0 := by nlinarith [hA0nn, hrjR]

lemma fiberPot_sub_update_eq {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {v : Cn n → ℂ}
    (hv : Continuous v) (z z' : Cn n) :
    fiberPot R j v z - fiberPot R j v (Function.update z j (z' j))
      = -((Real.pi : ℂ))⁻¹ * ((z j - z' j) *
          ∫ w in Metric.ball (0 : ℂ) R, v (Function.update z j w) / ((w - z j) * (w - z' j))) := by
  have hB' : (∫ w in Metric.ball (0:ℂ) R,
        v (Function.update (Function.update z j (z' j)) j w) / (w - Function.update z j (z' j) j))
      = ∫ w in Metric.ball (0:ℂ) R, v (Function.update z j w) / (w - z' j) := by
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    simp only [Function.update_idem, Function.update_self]
  have hpt : ∀ᵐ w ∂(volume : Measure ℂ), w ∈ Metric.ball 0 R →
      (v (Function.update z j w) / (w - z j) - v (Function.update z j w) / (w - z' j))
        = (z j - z' j) * (v (Function.update z j w) / ((w - z j) * (w - z' j))) := by
    have hnull : ∀ᵐ w : ℂ, w ≠ z j ∧ w ≠ z' j := by
      have h1 : ∀ᵐ w : ℂ, w ≠ z j := by
        rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (z j)
      have h2 : ∀ᵐ w : ℂ, w ≠ z' j := by
        rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (z' j)
      filter_upwards [h1, h2] with w hw1 hw2; exact ⟨hw1, hw2⟩
    filter_upwards [hnull] with w hw _
    obtain ⟨hw1, hw2⟩ := hw
    rw [div_sub_div _ _ (sub_ne_zero.mpr hw1) (sub_ne_zero.mpr hw2), ← mul_div_assoc]
    congr 1
    ring
  have key : (∫ w in Metric.ball 0 R,
        (v (Function.update z j w) / (w - z j) - v (Function.update z j w) / (w - z' j)))
      = (z j - z' j) * ∫ w in Metric.ball 0 R, v (Function.update z j w) / ((w - z j) * (w - z' j)) := by
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_ball hpt, MeasureTheory.integral_const_mul]
  have hA : IntegrableOn (fun w : ℂ => v (Function.update z j w) / (w - z j)) (Metric.ball 0 R) :=
    integrableOn_fiberIntegrand R j hv z
  have hB : IntegrableOn (fun w : ℂ => v (Function.update z j w) / (w - z' j)) (Metric.ball 0 R) := by
    simpa only [Function.update_idem, Function.update_self]
      using integrableOn_fiberIntegrand R j hv (Function.update z j (z' j))
  rw [fiberPot_apply, fiberPot_apply, hB', ← key, integral_sub hA hB]
  ring

lemma norm_fiberPot_sub_update_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r : Fin n → ℝ} (hrj0 : 0 < r j) (hrjR : r j < R)
    {v : Cn n → ℂ} (hv : Continuous v) {A0 K : ℝ} (hA0nn : 0 ≤ A0) (hKnn : 0 ≤ K)
    (hA0 : ∀ x ∈ fiberAccess r j R, ‖v x‖ ≤ A0)
    (hK : ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
        ‖a - b‖ * (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹) ≤ K * ‖a - b‖ ^ α)
    {z z' : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r)
    (hz' : z' ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    ‖fiberPot R j v z - fiberPot R j v (Function.update z j (z' j))‖
      ≤ (Real.pi⁻¹ * A0 * K) * ‖z - z'‖ ^ α := by
  rcases eq_or_ne (z j) (z' j) with hjj | hjj
  · have hupd : Function.update z j (z' j) = z := by
      rw [Function.update_eq_self_iff]; exact hjj.symm
    rw [hupd, sub_self, norm_zero]
    positivity
  · have hzj : ‖z j‖ ≤ r j := le_of_lt (by simpa using hz j)
    have hz'j : ‖z' j‖ ≤ r j := le_of_lt (by simpa using hz' j)
    have hInt : IntegrableOn (fun w : ℂ => (‖w - z j‖ * ‖w - z' j‖)⁻¹) (Metric.ball 0 R) :=
      integrableOn_inv_mul_inv_ball hjj
    have hmaj : Integrable (fun w : ℂ => A0 * (‖w - z j‖ * ‖w - z' j‖)⁻¹)
        (volume.restrict (Metric.ball 0 R)) := hInt.const_mul A0
    have hpt : ∀ᵐ w ∂(volume.restrict (Metric.ball 0 R)),
        ‖v (Function.update z j w) / ((w - z j) * (w - z' j))‖
          ≤ A0 * (‖w - z j‖ * ‖w - z' j‖)⁻¹ := by
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
      rw [norm_div, norm_mul, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hA0 _ (update_mem_fiberAccess hz hw)) (by positivity)
    have hbound : ‖∫ w in Metric.ball 0 R, v (Function.update z j w) / ((w - z j) * (w - z' j))‖
        ≤ A0 * (∫ w in Metric.ball 0 R, (‖w - z j‖ * ‖w - z' j‖)⁻¹) := by
      rw [← MeasureTheory.integral_const_mul]
      exact norm_integral_le_of_norm_le hmaj hpt
    have hδ : ‖z j - z' j‖ ≤ ‖z - z'‖ := by
      have h := norm_le_pi_norm (z - z') j
      simpa using h
    have hpow : ‖z j - z' j‖ ^ α ≤ ‖z - z'‖ ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hδ hα.le
    calc ‖fiberPot R j v z - fiberPot R j v (Function.update z j (z' j))‖
        = Real.pi⁻¹ * (‖z j - z' j‖ * ‖∫ w in Metric.ball 0 R, v (Function.update z j w) / ((w - z j) * (w - z' j))‖) := by
          rw [fiberPot_sub_update_eq hR j hv z z']
          rw [show -((Real.pi:ℂ))⁻¹ * ((z j - z' j) * ∫ w in Metric.ball 0 R, v (Function.update z j w) / ((w - z j) * (w - z' j)))
                = (-((Real.pi:ℂ))⁻¹) * ((z j - z' j) * ∫ w in Metric.ball 0 R, v (Function.update z j w) / ((w - z j) * (w - z' j))) by ring]
          rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_mul]
      _ ≤ Real.pi⁻¹ * (‖z j - z' j‖ * (A0 * (∫ w in Metric.ball 0 R, (‖w - z j‖ * ‖w - z' j‖)⁻¹))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) (by positivity)
      _ = Real.pi⁻¹ * A0 * (‖z j - z' j‖ * ∫ w in Metric.ball 0 R, (‖w - z j‖ * ‖w - z' j‖)⁻¹) := by ring
      _ ≤ Real.pi⁻¹ * A0 * (K * ‖z j - z' j‖ ^ α) := by
          refine mul_le_mul_of_nonneg_left (hK (z j) (z' j) hzj hz'j) (by positivity)
      _ = Real.pi⁻¹ * A0 * K * ‖z j - z' j‖ ^ α := by ring
      _ ≤ Real.pi⁻¹ * A0 * K * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_left hpow (by positivity)

lemma fiberPot_update_sub_eq {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {v : Cn n → ℂ}
    (hv : Continuous v) (z z' : Cn n) :
    fiberPot R j v (Function.update z j (z' j)) - fiberPot R j v z'
      = -((Real.pi : ℂ))⁻¹ *
          ∫ w in Metric.ball (0 : ℂ) R,
            (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j) := by
  have h1 : fiberPot R j v (Function.update z j (z' j))
      = -((Real.pi:ℂ))⁻¹ * ∫ w in Metric.ball 0 R, v (Function.update z j w) / (w - z' j) := by
    rw [fiberPot_apply]
    congr 1
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    simp only [Function.update_idem, Function.update_self]
  have hA : IntegrableOn (fun w : ℂ => v (Function.update z j w) / (w - z' j)) (Metric.ball 0 R) := by
    simpa only [Function.update_idem, Function.update_self]
      using integrableOn_fiberIntegrand R j hv (Function.update z j (z' j))
  have hB : IntegrableOn (fun w : ℂ => v (Function.update z' j w) / (w - z' j)) (Metric.ball 0 R) :=
    integrableOn_fiberIntegrand R j hv z'
  have hsub : (∫ w in Metric.ball (0:ℂ) R, v (Function.update z j w) / (w - z' j))
      - (∫ w in Metric.ball (0:ℂ) R, v (Function.update z' j w) / (w - z' j))
      = ∫ w in Metric.ball (0:ℂ) R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j) := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [sub_div]
  rw [h1, fiberPot_apply]
  rw [show -((Real.pi:ℂ))⁻¹ * (∫ w in Metric.ball 0 R, v (Function.update z j w) / (w - z' j))
        - -((Real.pi:ℂ))⁻¹ * (∫ w in Metric.ball 0 R, v (Function.update z' j w) / (w - z' j))
      = -((Real.pi:ℂ))⁻¹ * ((∫ w in Metric.ball 0 R, v (Function.update z j w) / (w - z' j))
        - (∫ w in Metric.ball 0 R, v (Function.update z' j w) / (w - z' j))) by ring]
  rw [hsub]

lemma norm_fiberPot_update_sub_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    {r : Fin n → ℝ} (hrj0 : 0 < r j) (hrjR : r j < R)
    {v : Cn n → ℂ} (hv : Continuous v) {K0 : ℝ} (hK0nn : 0 ≤ K0)
    (hK0 : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R, ‖v x - v y‖ ≤ K0 * ‖x - y‖ ^ α)
    {z z' : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r)
    (hz' : z' ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    ‖fiberPot R j v (Function.update z j (z' j)) - fiberPot R j v z'‖
      ≤ 2 * (R + r j) * (K0 * ‖z - z'‖ ^ α) := by
  rw [fiberPot_update_sub_eq hR j hv z z']
  have hz'j : ‖z' j‖ ≤ r j := le_of_lt (by simpa using hz' j)
  have hInt : Integrable (fun w : ℂ => (‖w - z' j‖)⁻¹) (volume.restrict (Metric.ball 0 R)) := by
    have h := (integrableOn_sub_inv_ball R (z' j)).norm
    simpa only [norm_inv] using h
  have hpt : ∀ᵐ w ∂(volume.restrict (Metric.ball 0 R)),
      ‖(v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j)‖
        ≤ K0 * ‖z - z'‖ ^ α * (‖w - z' j‖)⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
    rw [norm_div, div_eq_mul_inv]
    have hxy : ‖Function.update z j w - Function.update z' j w‖ ≤ ‖z - z'‖ :=
      norm_update_sub_update_le z z' j w
    have hb := hK0 _ (update_mem_fiberAccess hz hw) _ (update_mem_fiberAccess hz' hw)
    have hb' : ‖v (Function.update z j w) - v (Function.update z' j w)‖ ≤ K0 * ‖z - z'‖ ^ α :=
      hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hxy hα.le) hK0nn)
    exact mul_le_mul_of_nonneg_right hb' (by positivity)
  have hmaj : Integrable (fun w : ℂ => K0 * ‖z - z'‖ ^ α * (‖w - z' j‖)⁻¹)
      (volume.restrict (Metric.ball 0 R)) := hInt.const_mul _
  have hbound : ‖∫ w in Metric.ball 0 R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j)‖
      ≤ K0 * ‖z - z'‖ ^ α * (∫ w in Metric.ball 0 R, (‖w - z' j‖)⁻¹) := by
    rw [← MeasureTheory.integral_const_mul]
    exact norm_integral_le_of_norm_le hmaj hpt
  have hkey : (∫ w in Metric.ball 0 R, (‖w - z' j‖)⁻¹) ≤ 2 * Real.pi * (R + r j) :=
    integral_inv_sub_ball_le hR (le_of_lt hrj0) hrjR (z' j) hz'j
  have hnn : 0 ≤ K0 * ‖z - z'‖ ^ α := mul_nonneg hK0nn (Real.rpow_nonneg (norm_nonneg _) α)
  calc ‖-((Real.pi:ℂ))⁻¹ * ∫ w in Metric.ball 0 R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j)‖
      = Real.pi⁻¹ * ‖∫ w in Metric.ball 0 R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j)‖ := by
        rw [show -((Real.pi:ℂ))⁻¹ * (∫ w in Metric.ball 0 R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j))
              = (-((Real.pi:ℂ))⁻¹) * (∫ w in Metric.ball 0 R, (v (Function.update z j w) - v (Function.update z' j w)) / (w - z' j)) by ring]
        rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    _ ≤ Real.pi⁻¹ * (K0 * ‖z - z'‖ ^ α * (2 * Real.pi * (R + r j))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hbound.trans (mul_le_mul_of_nonneg_left hkey hnn)
    _ = 2 * (R + r j) * (K0 * ‖z - z'‖ ^ α) := by
        rw [show Real.pi⁻¹ * (K0 * ‖z - z'‖ ^ α * (2 * Real.pi * (R + r j)))
              = K0 * ‖z - z'‖ ^ α * (R + r j) * (Real.pi⁻¹ * (2 * Real.pi)) by ring]
        rw [show Real.pi⁻¹ * (2 * Real.pi) = 2 by
          rw [mul_comm (2:ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]]
        ring

lemma norm_fiberPot_sub_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α) (hα1 : α < 1)
    {r : Fin n → ℝ} (hrj0 : 0 < r j) (hrjR : r j < R)
    {v : Cn n → ℂ} (hv : Continuous v) {A0 K0 K : ℝ} (hA0nn : 0 ≤ A0) (hK0nn : 0 ≤ K0) (hKnn : 0 ≤ K)
    (hA0 : ∀ x ∈ fiberAccess r j R, ‖v x‖ ≤ A0)
    (hK0 : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R, ‖v x - v y‖ ≤ K0 * ‖x - y‖ ^ α)
    (hK : ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
        ‖a - b‖ * (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹) ≤ K * ‖a - b‖ ^ α)
    {z z' : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r)
    (hz' : z' ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    ‖fiberPot R j v z - fiberPot R j v z'‖
      ≤ (Real.pi⁻¹ * A0 * K + 2 * (R + r j) * K0) * ‖z - z'‖ ^ α := by
  have h1 := norm_fiberPot_sub_update_le hR j hα hα1 hrj0 hrjR hv hA0nn hKnn hA0 hK hz hz'
  have h2 := norm_fiberPot_update_sub_le hR j hα hrj0 hrjR hv hK0nn hK0 hz hz'
  have hsplit : fiberPot R j v z - fiberPot R j v z'
      = (fiberPot R j v z - fiberPot R j v (Function.update z j (z' j)))
        + (fiberPot R j v (Function.update z j (z' j)) - fiberPot R j v z') := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2' : ‖fiberPot R j v (Function.update z j (z' j)) - fiberPot R j v z'‖
      ≤ (2 * (R + r j) * K0) * ‖z - z'‖ ^ α := h2.trans (le_of_eq (by ring))
  exact (add_le_add h1 h2').trans (le_of_eq (by ring))

lemma main_of_twoPole {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α) (hα1 : α < 1)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R)
    {K : ℝ} (hKnn : 0 ≤ K)
    (hK : ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
        ‖a - b‖ * (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹) ≤ K * ‖a - b‖ ^ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Cn n → ℂ, ContDiff ℝ 0 v → fiberBand R j v →
      Work.CR.Flat.holderNorm 0 α (fiberPot R j v) (Work.CR.Flat.polydisc (0 : Cn n) r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm 0 α v (fiberAccess r j R) := by
  have hrj0 : 0 < r j := hr j
  have hrjR : r j < R := hrR j
  set C1 : ℝ := Real.pi⁻¹ * K + 2 * (R + r j) with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; positivity
  refine ⟨4 * R + C1, by positivity, ?_⟩
  intro v hv hband
  have hvc : Continuous v := hv.continuous
  set S : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 0 v (fiberAccess r j R) with hS
  set H : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 0 α v (fiberAccess r j R) with hH
  have hHN : Work.CR.Flat.holderNorm 0 α v (fiberAccess r j R) = S + H := by
    rw [holderNorm_zero_eq', hS, hH]
  by_cases hStop : S = ⊤
  · rw [hHN, hStop, top_add]
    rw [ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
    exact le_top
  by_cases hHtop : H = ⊤
  · rw [hHN, hHtop, add_top]
    rw [ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
    exact le_top
  set A0 : ℝ := S.toReal with hA0def
  set K0 : ℝ := H.toReal with hK0def
  have hA0nn : 0 ≤ A0 := hA0def ▸ ENNReal.toReal_nonneg
  have hK0nn : 0 ≤ K0 := hK0def ▸ ENNReal.toReal_nonneg
  have hSeq : ENNReal.ofReal A0 = S := hA0def ▸ ENNReal.ofReal_toReal hStop
  have hHeq : ENNReal.ofReal K0 = H := hK0def ▸ ENNReal.ofReal_toReal hHtop
  have hvA : ∀ x ∈ fiberAccess r j R, ‖v x‖ ≤ A0 := by
    intro x hx
    have h1 : ENNReal.ofReal ‖v x‖ ≤ S := by
      rw [hS, Work.CR.Flat.iterDerivNorm_zero]
      exact le_iSup₂_of_le x hx le_rfl
    rw [← hSeq] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hA0nn).mp h1
  have hvK : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R, ‖v x - v y‖ ≤ K0 * ‖x - y‖ ^ α := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow (ne_of_gt hα)]
    · have h3 : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have h1 : ENNReal.ofReal (‖v x - v y‖ / ‖x - y‖ ^ α) ≤ H := by
        rw [hH]
        have h := Work.CR.Flat.le_holderSeminorm 0 α v (fiberAccess r j R) hx hy hxy
        rwa [norm_iteratedFDerivWithin_zero_sub' v (fiberAccess r j R) x y] at h
      have h2 : ‖v x - v y‖ / ‖x - y‖ ^ α ≤ K0 :=
        (ENNReal.ofReal_le_ofReal_iff hK0nn).mp (by rw [hHeq]; exact h1)
      rwa [div_le_iff₀ h3] at h2
  have hsup : Work.CR.Flat.iterDerivNorm 0 (fiberPot R j v) (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal (4 * R * A0) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z hz => ?_
    exact ENNReal.ofReal_le_ofReal (norm_fiberPot_le hR j hrj0 hrjR hvc hA0nn hvA hz)
  have hsem : Work.CR.Flat.holderSeminorm 0 α (fiberPot R j v) (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal C1 * (S + H) := by
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz' => ?_
    rw [norm_iteratedFDerivWithin_zero_sub' (fiberPot R j v) (Work.CR.Flat.polydisc (0 : Cn n) r) z z']
    have hb := norm_fiberPot_sub_le hR j hα hα1 hrj0 hrjR hvc hA0nn hK0nn hKnn hvA hvK hK hz hz'
    have h3 : 0 < ‖z - z'‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz')) α
    have hb2 : ‖fiberPot R j v z - fiberPot R j v z'‖ / ‖z - z'‖ ^ α ≤ C1 * (A0 + K0) := by
      rw [div_le_iff₀ h3, hC1def]
      have hle : (Real.pi⁻¹ * A0 * K + 2 * (R + r j) * K0) * ‖z - z'‖ ^ α
          ≤ ((Real.pi⁻¹ * K + 2 * (R + r j)) * (A0 + K0)) * ‖z - z'‖ ^ α := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α)
        have hc1 : 0 ≤ Real.pi⁻¹ * K := by positivity
        have hc2 : 0 ≤ (2 : ℝ) * (R + r j) := by positivity
        nlinarith [hA0nn, hK0nn, hc1, hc2]
      exact hb.trans hle
    calc ENNReal.ofReal (‖fiberPot R j v z - fiberPot R j v z'‖ / ‖z - z'‖ ^ α)
        ≤ ENNReal.ofReal (C1 * (A0 + K0)) := ENNReal.ofReal_le_ofReal hb2
      _ = ENNReal.ofReal C1 * ENNReal.ofReal (A0 + K0) :=
            ENNReal.ofReal_mul hC1nn
      _ = ENNReal.ofReal C1 * (ENNReal.ofReal A0 + ENNReal.ofReal K0) := by
            rw [ENNReal.ofReal_add hA0nn hK0nn]
      _ = ENNReal.ofReal C1 * (S + H) := by rw [hSeq, hHeq]
  have hmain : Work.CR.Flat.holderNorm 0 α (fiberPot R j v) (Work.CR.Flat.polydisc (0 : Cn n) r)
      ≤ ENNReal.ofReal (4 * R + C1) * (S + H) := by
    rw [holderNorm_zero_eq']
    refine (add_le_add hsup hsem).trans ?_
    calc ENNReal.ofReal (4 * R * A0) + ENNReal.ofReal C1 * (S + H)
        = ENNReal.ofReal (4 * R) * S + ENNReal.ofReal C1 * (S + H) := by
          rw [← hSeq, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (4 * R) * (S + H) + ENNReal.ofReal C1 * (S + H) := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left (le_add_right le_rfl) bot_le
      _ = (ENNReal.ofReal (4 * R) + ENNReal.ofReal C1) * (S + H) := by rw [add_mul]
      _ = ENNReal.ofReal (4 * R + C1) * (S + H) := by
          rw [ENNReal.ofReal_add (by positivity) hC1nn]
  rw [hHN]
  exact hmain



/-- The order-zero estimate for the fixed-disc potential: for data supported in the band `‖z j‖ < R` (no bound on the transverse support), the `C^{0,α}` norm of `fiberPot R j v` on `polydisc 0 r` is controlled by the `C^{0,α}` norm of `v` on the access polydisc `fiberAccess r j R = polydisc 0 (Function.update r j R)` (the polydisc read by the potential).

Suggested route. The sup bound is `‖fiberPot R j v z‖ ≤ π⁻¹ sup_{A}‖v‖ ∫_{‖w‖<R} ‖w - z j‖⁻¹ dw ≤ C sup`. For the Hölder seminorm, write the difference at `z, z' ∈ polydisc 0 r` as a fibre difference plus a transverse difference via the intermediate point `(z_i)_{i≠j}, z'_j`. The fibre difference is bounded by `Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le` applied to the slice, using `fiberPot_eq_cauchyTransform`; this needs the *global* `α`-Hölder constant of the slice, which is controlled by `(sup, α-seminorm)` of `v` on `A` (the slice is continuous with support in `ball 0 R` and its `α`-seminorm over that ball is the `α`-seminorm of `v` on `A`; use a geometric decay argument to reach the boundary). The transverse difference is elementary: the kernels agree and the integrand difference is bounded by the `α`-seminorm of `v` on `A` times `‖z - z'‖^α`. -/
theorem holderNorm_zero_fiberPot_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Cn n → ℂ, ContDiff ℝ 0 v → fiberBand R j v →
      Work.CR.Flat.holderNorm 0 α (fiberPot R j v) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm 0 α v (fiberAccess r j R) := by
  obtain ⟨K, hKpos, hK⟩ :=
    twoPoleKernel_integral_mul_le (R := R) (α := α) (r0 := r j) hR (hr j).le (hrR j) hα hα1
  exact main_of_twoPole hR j hα hα1 hr hrR hKpos.le hK

end Work.NN.Core
