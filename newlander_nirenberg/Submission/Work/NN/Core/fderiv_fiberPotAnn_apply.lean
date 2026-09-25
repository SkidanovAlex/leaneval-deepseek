import Mathlib
import Submission.Work.NN.Core.VanishingDefs

/-!
# The derivative of the annulus potential `fiberPotAnn` in the base point

This file proves `Work.NN.Core.fderiv_fiberPotAnn_apply`: the real derivative of the annulus
potential

  `fiberPotAnn j l A η z = -(1/π) ∫_{w ∈ A} η (z with z j := w) (w - z j)^{-(l+1)} dw`

in the base point `z` is obtained by differentiating under the integral sign:

  `fderiv ℝ (fiberPotAnn j l A η) x v
     = fiberPotAnn j l A (fun y => fderiv ℝ η y (v with v j := 0)) x
       + (l+1) (v j) fiberPotAnn j (l+1) A η x`.

The analytic content is the usual dominated convergence theorem for a parameter integral
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`).  The two hypotheses that make the domination
uniform are that the pole `z j` stays away from `A` (`hAd` together with `hMs`), which supplies a
positive lower bound for `‖w - z j‖` on a whole neighbourhood of the base point, and the bounds
`hM`, `hM'` on the datum and its derivative.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Work.NN.Core

/-- The `j`-th coordinate projection `z ↦ z j` as a real-linear functional. -/
def coordCLM {n : ℕ} (j : Fin n) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) j

@[simp] lemma coordCLM_apply {n : ℕ} (j : Fin n) (z : Fin n → ℂ) : coordCLM j z = z j := rfl

lemma norm_coordCLM_le {n : ℕ} (j : Fin n) : ‖coordCLM j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul, coordCLM_apply]
  exact norm_le_pi_norm x j

/-- `‖c • L‖ ≤ ‖c‖ ‖L‖` for complex multiples of real-linear functionals. -/
lemma norm_smul_clm_le {n : ℕ} (c : ℂ) (L : (Fin n → ℂ) →L[ℝ] ℂ) : ‖c • L‖ ≤ ‖c‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [smul_apply, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖L v‖ ≤ ‖c‖ * (‖L‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm L v) (norm_nonneg c)
    _ = ‖c‖ * ‖L‖ * ‖v‖ := by ring

lemma norm_updateZero_le {n : ℕ} (j : Fin n) : ‖updateZero j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul, updateZero_apply]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i => by
    by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne h]; exact norm_le_pi_norm x i)

lemma smul_id_comp {n : ℕ} (c : ℂ) (L : (Fin n → ℂ) →L[ℝ] ℂ) :
    (c • ContinuousLinearMap.id ℝ ℂ) ∘SL L = c • L := by
  ext v
  simp [smul_apply]

/-- The real derivative of `z ↦ ((w - z j)⁻¹)^(l+1)`.  Since the function has a pole at `z j = w`
the statement is conditional on `w ≠ x j`. -/
lemma hasFDerivAt_inv_pow_update {n : ℕ} (j : Fin n) (l : ℕ) (w : ℂ) {x : Fin n → ℂ}
    (hx : w ≠ x j) :
    HasFDerivAt (fun z : Fin n → ℂ => ((w - z j)⁻¹) ^ (l + 1))
      (((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2)) • (coordCLM j)) x := by
  have hu₀ : w - x j ≠ 0 := sub_ne_zero.mpr hx
  have hψ : HasFDerivAt (fun z : Fin n → ℂ => w - z j) (-(coordCLM j)) x := by
    have h : HasFDerivAt (fun z : Fin n → ℂ => z j) (coordCLM j) x := coordCLM j |>.hasFDerivAt
    simpa using h.const_sub w
  have hinv : HasFDerivAt (fun u : ℂ => u⁻¹)
      ((-((w - x j)⁻¹)^2) • ContinuousLinearMap.id ℝ ℂ) (w - x j) := by
    have h := hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) (x := (w - x j)) hu₀
    convert h using 2
    ext t
    simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  have hpow := hinv.pow (l + 1)
  have hC : (((l + 1) • ((w - x j)⁻¹) ^ (l + 1 - 1)) •
        ((-((w - x j)⁻¹)^2) • ContinuousLinearMap.id ℝ ℂ))
      = (-((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2))) • ContinuousLinearMap.id ℝ ℂ := by
    rw [smul_smul, nsmul_eq_mul, show l + 1 - 1 = l from Nat.add_sub_cancel l 1, pow_add]
    congr 1
    push_cast
    ring
  have hcomp := hpow.comp x hψ
  refine hcomp.congr_fderiv ?_
  rw [hC, smul_id_comp]
  simp only [smul_neg, neg_smul, neg_neg]

/-- The integrand of the annulus potential. -/
private def annIntegrand {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)

/-- The candidate derivative of `annIntegrand` in the base point. -/
private def annDeriv {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  (η (Function.update z j w)) • (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))
    + (((w - z j)⁻¹) ^ (l + 1)) • ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))

/-- The real-linear map `L ↦ L ∘ updateZero j` is continuous. -/
lemma continuous_comp_updateZero {n : ℕ} (j : Fin n) :
    Continuous fun L : (Fin n → ℂ) →L[ℝ] ℂ => L.comp (updateZero j) := by
  have h := ((ContinuousLinearMap.compL ℝ (Fin n → ℂ) (Fin n → ℂ) ℂ).flip (updateZero j)).continuous
  convert h using 1
  ext L v
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

lemma isFiniteMeasure_restrict_of_lt_top {A : Set ℂ} (hAfin : volume A < ⊤) :
    IsFiniteMeasure (volume.restrict A) := by
  refine ⟨?_⟩
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact hAfin

theorem fderiv_fiberPotAnn_apply {n : ℕ} {j : Fin n} {l : ℕ} {A : Set ℂ} {η : (Fin n → ℂ) → ℂ}
    (hη : ContDiff ℝ 1 η) (hA : MeasurableSet A) (hAfin : MeasureTheory.volume A < ⊤)
    {s : Set (Fin n → ℂ)} {x : Fin n → ℂ} (hs : s ∈ nhds x) {d M M' : ℝ} (hd : 0 < d)
    (hM0 : 0 ≤ M) (hM0' : 0 ≤ M') (hAd : ∀ w ∈ A, d ≤ ‖w‖) (hMs : ∀ z ∈ s, ‖z j‖ < d)
    (hM : ∀ z ∈ s, ∀ w ∈ A, ‖η (Function.update z j w)‖ ≤ M)
    (hM' : ∀ z ∈ s, ∀ w ∈ A, ‖fderiv ℝ η (Function.update z j w)‖ ≤ M')
    (v : Fin n → ℂ) :
    fderiv ℝ (Work.NN.Core.fiberPotAnn j l A η) x v
      = Work.NN.Core.fiberPotAnn j l A (fun y => fderiv ℝ η y (Function.update v j 0)) x
        + (l + 1) * (v j) * Work.NN.Core.fiberPotAnn j (l + 1) A η x := by
  have hxmem : x ∈ s := mem_of_mem_nhds hs
  have hxd : ‖x j‖ < d := hMs x hxmem
  -- the radius of the neighbourhood on which the pole stays away from `A`
  set δ : ℝ := (d - ‖x j‖) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hxδ : ‖x j‖ + δ < d := by rw [hδdef]; linarith
  set T : Set (Fin n → ℂ) := Metric.ball x δ ∩ s with hTdef
  have hTnhds : T ∈ nhds x := by
    rw [hTdef]
    exact Filter.inter_mem (Metric.ball_mem_nhds x hδpos) hs
  have hxT : x ∈ T := by
    rw [hTdef]
    exact ⟨by simp [Metric.mem_ball, hδpos], hxmem⟩
  have hTsub : ∀ z ∈ T, z ∈ s := fun z hz => (by simpa [hTdef] using hz : z ∈ Metric.ball x δ ∧ z ∈ s).2
  have hTball : ∀ z ∈ T, z ∈ Metric.ball x δ :=
    fun z hz => (by simpa [hTdef] using hz : z ∈ Metric.ball x δ ∧ z ∈ s).1
  -- control of the `j`-th coordinate and separation from `A`
  have hzj : ∀ z ∈ T, ‖z j‖ ≤ ‖x j‖ + δ := by
    intro z hz
    have hzd : ‖z - x‖ < δ := by
      have h := hTball z hz
      simpa [Metric.mem_ball, dist_eq_norm] using h
    have h2 : ‖z j - x j‖ ≤ ‖z - x‖ := norm_le_pi_norm (z - x) j
    calc ‖z j‖ = ‖(z j - x j) + x j‖ := by ring_nf
      _ ≤ ‖z j - x j‖ + ‖x j‖ := norm_add_le _ _
      _ ≤ ‖z - x‖ + ‖x j‖ := by linarith
      _ ≤ ‖x j‖ + δ := by linarith
  have hsep : ∀ z ∈ T, ∀ w ∈ A, δ ≤ ‖w - z j‖ := by
    intro z hz w hw
    have h1 : d ≤ ‖w‖ := hAd w hw
    have h2 : ‖z j‖ ≤ ‖x j‖ + δ := hzj z hz
    calc δ = d - (‖x j‖ + δ) := by rw [hδdef]; ring
      _ ≤ ‖w‖ - ‖z j‖ := by linarith
      _ ≤ ‖w - z j‖ := norm_sub_norm_le w (z j)
  have hsepx : ∀ w ∈ A, δ ≤ ‖w - x j‖ := fun w hw => hsep x hxT w hw
  have hwne : ∀ z ∈ T, ∀ w ∈ A, w ≠ z j := by
    intro z hz w hw h
    have h1 : d ≤ ‖w‖ := hAd w hw
    have h2 : ‖z j‖ ≤ ‖x j‖ + δ := hzj z hz
    rw [h] at h1
    linarith
  -- the dominating constant
  set C : ℝ := M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) + M' * (δ⁻¹) ^ (l + 1) with hCdef
  -- basic bounds
  have hk1 : ∀ z ∈ T, ∀ w ∈ A, ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (δ⁻¹) ^ (l + 1) := by
    intro z hz w hw
    have h := hsep z hz w hw
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [norm_inv]
    exact inv_anti₀ hδpos h
  have hk2 : ∀ z ∈ T, ∀ w ∈ A, ‖((w - z j)⁻¹) ^ (l + 2)‖ ≤ (δ⁻¹) ^ (l + 2) := by
    intro z hz w hw
    have h := hsep z hz w hw
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [norm_inv]
    exact inv_anti₀ hδpos h
  have hAnorm : ∀ z ∈ T, ∀ w ∈ A,
      ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖ ≤ M' := by
    intro z hz w hw
    calc ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖
        ≤ ‖fderiv ℝ η (Function.update z j w)‖ * ‖updateZero j‖ :=
          ContinuousLinearMap.opNorm_comp_le (h := fderiv ℝ η (Function.update z j w))
            (updateZero j)
      _ ≤ M' * 1 := mul_le_mul (hM' z (hTsub z hz) w hw) (norm_updateZero_le j) (norm_nonneg _) hM0'
      _ = M' := mul_one M'
  -- measurability of the integrands
  have hFmeas : ∀ z, Measurable (fun w : ℂ => annIntegrand j l η z w) := by
    intro z
    simp only [annIntegrand]
    exact ((hη.continuous.measurable.comp (continuous_update z j).measurable)).mul
      (((measurable_id.sub measurable_const).inv).pow_const (l + 1))
  have hLmeas : ∀ z, Measurable fun w : ℂ =>
      (fderiv ℝ η (Function.update z j w)).comp (updateZero j) := by
    intro z
    have hcont : Continuous fun w : ℂ => fderiv ℝ η (Function.update z j w) :=
      (hη.continuous_fderiv one_ne_zero).comp (continuous_update z j)
    exact (continuous_comp_updateZero j).measurable.comp hcont.measurable
  have hF'meas : ∀ z, Measurable (fun w : ℂ => annDeriv j l η z w) := by
    intro z
    have hηz : Measurable fun w : ℂ => η (Function.update z j w) :=
      hη.continuous.measurable.comp (continuous_update z j).measurable
    have hsc : Measurable fun w : ℂ =>
        ((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2) : ℂ) :=
      measurable_const.mul (((measurable_id.sub measurable_const).inv).pow_const (l + 2))
    have hk1m : Measurable fun w : ℂ => (((w - z j)⁻¹) ^ (l + 1) : ℂ) :=
      ((measurable_id.sub measurable_const).inv).pow_const (l + 1)
    refine Measurable.add ?_ ?_
    · exact hηz.smul (hsc.smul (measurable_const : Measurable fun _ : ℂ => coordCLM j))
    · exact hk1m.smul (hLmeas z)
  haveI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict_of_lt_top hAfin
  -- integrability of the integrand at the base point
  have hInt : Integrable (fun w : ℂ => annIntegrand j l η x w) (volume.restrict A) := by
    refine MeasureTheory.Integrable.of_bound (hFmeas x).aestronglyMeasurable (M * (δ⁻¹) ^ (l + 1)) ?_
    filter_upwards [self_mem_ae_restrict hA] with w hw
    simp only [annIntegrand]
    calc ‖η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 1)‖
        = ‖η (Function.update x j w)‖ * ‖((w - x j)⁻¹) ^ (l + 1)‖ := norm_mul _ _
      _ ≤ M * (δ⁻¹) ^ (l + 1) :=
          mul_le_mul (hM x hxmem w hw)
            (hk1 x hxT w hw) (norm_nonneg _) hM0
  -- the pointwise derivative of the integrand
  have hFpoint : ∀ᵐ (w : ℂ) ∂(volume.restrict A), ∀ z ∈ T,
      HasFDerivAt (fun y : Fin n → ℂ => annIntegrand j l η y w) (annDeriv j l η z w) z := by
    filter_upwards [self_mem_ae_restrict hA] with w hw z hz
    have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
    have h1 : HasFDerivAt (fun y : Fin n → ℂ => η (Function.update y j w))
        ((fderiv ℝ η (Function.update z j w)).comp (updateZero j)) z :=
      (hηd.differentiableAt.hasFDerivAt).comp z (hasFDerivAt_update_ann j w z)
    have h2 := hasFDerivAt_inv_pow_update j l w (hwne z hz w hw) (x := z)
    have h3 := h1.mul h2
    have hfe : (fun y : Fin n → ℂ => η (Function.update y j w) * ((w - y j)⁻¹) ^ (l + 1))
        =ᶠ[𝓝 z] ((fun y : Fin n → ℂ => η (Function.update y j w)) *
          fun y => ((w - y j)⁻¹) ^ (l + 1)) :=
      Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]
    have h4 := (hfe.hasFDerivAt_iff).mpr h3
    simpa only [annIntegrand, annDeriv] using h4
  -- the domination of the derivative integrand
  have hbound : ∀ᵐ (w : ℂ) ∂(volume.restrict A), ∀ z ∈ T, ‖annDeriv j l η z w‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict hA] with w hw z hz
    have h1 : ‖(η (Function.update z j w)) •
        (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
        ≤ M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) := by
      calc ‖(η (Function.update z j w)) •
            (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
          ≤ ‖η (Function.update z j w)‖ *
              ‖(((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖ :=
            norm_smul_clm_le _ _
        _ ≤ M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) := by
            refine mul_le_mul (hM z (hTsub z hz) w hw) ?_ (norm_nonneg _) hM0
            refine le_trans (norm_smul_clm_le _ _) ?_
            refine le_trans (mul_le_mul_of_nonneg_left (norm_coordCLM_le j) (norm_nonneg _)) ?_
            rw [mul_one, norm_mul]
            exact mul_le_mul_of_nonneg_left (hk2 z hz w hw) (norm_nonneg _)
    have h2 : ‖(((w - z j)⁻¹) ^ (l + 1)) •
        ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))‖
        ≤ M' * (δ⁻¹) ^ (l + 1) := by
      refine le_trans (norm_smul_clm_le _ _) ?_
      calc ‖((w - z j)⁻¹) ^ (l + 1)‖ *
            ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖
          ≤ (δ⁻¹) ^ (l + 1) * M' :=
            mul_le_mul (hk1 z hz w hw) (hAnorm z hz w hw) (norm_nonneg _) (by positivity)
        _ = M' * (δ⁻¹) ^ (l + 1) := by ring
    calc ‖annDeriv j l η z w‖
        ≤ ‖(η (Function.update z j w)) •
              (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
          + ‖(((w - z j)⁻¹) ^ (l + 1)) •
              ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))‖ := by
          rw [annDeriv]; exact norm_add_le _ _
      _ ≤ C := by rw [hCdef]; linarith
  -- the dominating function is integrable
  have hboundint : Integrable (fun _ : ℂ => C) (volume.restrict A) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr inferInstance
  -- differentiation under the integral sign
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume.restrict A)
    (F := fun z w => annIntegrand j l η z w)
    (F' := fun z w => annDeriv j l η z w)
    (x₀ := x) (bound := fun _ => C) (s := T)
    hTnhds (Filter.Eventually.of_forall fun z => (hFmeas z).aestronglyMeasurable) hInt
    ((hF'meas x).aestronglyMeasurable) hbound hboundint hFpoint
  have hInt' : Integrable (fun w : ℂ => annDeriv j l η x w) (volume.restrict A) := by
    refine MeasureTheory.Integrable.of_bound (hF'meas x).aestronglyMeasurable C ?_
    filter_upwards [hbound] with w hw
    exact hw x hxT
  have hpot : fiberPotAnn j l A η
      = fun z => -((Real.pi : ℂ))⁻¹ * ∫ w in A, annIntegrand j l η z w := by
    funext z
    rw [fiberPotAnn_apply]
    rfl
  have hderiv : HasFDerivAt (fiberPotAnn j l A η)
      ((-((Real.pi : ℂ))⁻¹) • (∫ w in A, annDeriv j l η x w)) x := by
    rw [hpot]
    exact hmain.const_mul _
  -- evaluation at `v`
  have hLv : ((-((Real.pi : ℂ))⁻¹) • (∫ w in A, annDeriv j l η x w)) v
      = -((Real.pi : ℂ))⁻¹ * ∫ w in A, (annDeriv j l η x w) v := by
    rw [smul_apply, smul_eq_mul, ContinuousLinearMap.integral_apply hInt' v]
  -- the value of the derivative integrand
  have hpoint : ∀ w : ℂ, (annDeriv j l η x w) v
      = (fderiv ℝ η (Function.update x j w)) (Function.update v j 0) *
          ((w - x j)⁻¹) ^ (l + 1)
        + (l + 1) * (v j) * (η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)) := by
    intro w
    simp only [annDeriv, smul_apply, add_apply, coordCLM_apply,
      ContinuousLinearMap.comp_apply, updateZero_apply, smul_eq_mul]
    ring
  -- integrands of the two summands
  have hG1int : Integrable (fun w : ℂ => (fderiv ℝ η (Function.update x j w))
      (Function.update v j 0) * ((w - x j)⁻¹) ^ (l + 1)) (volume.restrict A) := by
    have hm : Measurable fun w : ℂ => (fderiv ℝ η (Function.update x j w))
        (Function.update v j 0) * ((w - x j)⁻¹) ^ (l + 1) :=
      (((hη.continuous_fderiv one_ne_zero).comp (continuous_update x j)).clm_apply
        continuous_const).measurable.mul
        (((measurable_id.sub measurable_const).inv).pow_const (l + 1))
    refine MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable
      (M' * ‖v‖ * (δ⁻¹) ^ (l + 1)) ?_
    filter_upwards [self_mem_ae_restrict hA] with w hw
    have h1 : ‖(fderiv ℝ η (Function.update x j w)) (Function.update v j 0)‖
        ≤ M' * ‖v‖ := by
      calc ‖(fderiv ℝ η (Function.update x j w)) (Function.update v j 0)‖
          ≤ ‖fderiv ℝ η (Function.update x j w)‖ * ‖Function.update v j 0‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M' * ‖v‖ := by
            refine mul_le_mul (hM' x hxmem w hw) ?_ (norm_nonneg _) hM0'
            calc ‖Function.update v j 0‖ = ‖updateZero j v‖ := by rw [updateZero_apply]
              _ ≤ ‖updateZero j‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (norm_updateZero_le j) (norm_nonneg v)
              _ = ‖v‖ := one_mul _
    calc ‖(fderiv ℝ η (Function.update x j w)) (Function.update v j 0) *
            ((w - x j)⁻¹) ^ (l + 1)‖
        = ‖(fderiv ℝ η (Function.update x j w)) (Function.update v j 0)‖ *
            ‖((w - x j)⁻¹) ^ (l + 1)‖ := norm_mul _ _
      _ ≤ (M' * ‖v‖) * (δ⁻¹) ^ (l + 1) :=
          mul_le_mul h1 (hk1 x hxT w hw) (norm_nonneg _) (mul_nonneg hM0' (norm_nonneg v))
      _ = M' * ‖v‖ * (δ⁻¹) ^ (l + 1) := by ring
  have hG2int : Integrable (fun w : ℂ => (l + 1) * (v j) *
      (η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2))) (volume.restrict A) := by
    have hm1 : Measurable fun _ : ℂ => (l + 1) * (v j) := measurable_const
    have hm2 : Measurable fun w : ℂ => η (Function.update x j w) :=
      hη.continuous.measurable.comp (continuous_update x j).measurable
    have hm3 : Measurable fun w : ℂ => ((w - x j)⁻¹) ^ (l + 2) :=
      ((measurable_id.sub measurable_const).inv).pow_const (l + 2)
    have hm : Measurable fun w : ℂ => (l + 1) * (v j) *
        (η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)) := hm1.mul (hm2.mul hm3)
    refine MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable
      (‖(l + 1 : ℂ)‖ * ‖v‖ * (M * (δ⁻¹) ^ (l + 2))) ?_
    filter_upwards [self_mem_ae_restrict hA] with w hw
    have h1 : ‖η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)‖ ≤ M * (δ⁻¹) ^ (l + 2) := by
      calc ‖η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)‖
          = ‖η (Function.update x j w)‖ * ‖((w - x j)⁻¹) ^ (l + 2)‖ := norm_mul _ _
        _ ≤ M * (δ⁻¹) ^ (l + 2) :=
            mul_le_mul (hM x hxmem w hw) (hk2 x hxT w hw) (norm_nonneg _) hM0
    have hvj : ‖v j‖ ≤ ‖v‖ := norm_le_pi_norm v j
    calc ‖(l + 1) * (v j) * (η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2))‖
        = ‖(l + 1 : ℂ)‖ * ‖v j‖ * ‖η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖(l + 1 : ℂ)‖ * ‖v‖ * (M * (δ⁻¹) ^ (l + 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hvj (norm_nonneg _)) h1 (by positivity) ?_
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- splitting the integral
  have hsplit : ∫ w in A, (annDeriv j l η x w) v
      = (∫ w in A, (fderiv ℝ η (Function.update x j w)) (Function.update v j 0) *
            ((w - x j)⁻¹) ^ (l + 1))
        + (l + 1) * (v j) * (∫ w in A, η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 2)) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add hG1int hG2int]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    exact hpoint w
  rw [hderiv.fderiv, hLv, hsplit]
  simp only [fiberPotAnn_apply]
  ring

end Work.NN.Core
