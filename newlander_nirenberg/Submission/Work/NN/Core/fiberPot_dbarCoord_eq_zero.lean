import Mathlib
import Submission.Work.NN.Core.fiberPot

/-!
# `∂̄_j (fiberPot R j V) = 0` when the data vanish near the slice of the base point

This file proves `Work.NN.Core.fiberPot_dbarCoord_eq_zero`: if the data `V` vanish on a neighbourhood
of the `j`-slice through `z`, then the fixed-disc potential `fiberPot R j V` is real differentiable
at `z` and its `j`-th `∂̄`-derivative vanishes there.

The proof is elementary once one notices that the moving singularity of the Cauchy kernel is
*shielded* by the vanishing of the data: writing `Φ x w = V (x with x_j replaced by w) * (w - x_j)⁻¹`,
the unique singularity `w = x j` of `Φ x w` lies in the ball `‖w - x j‖ < δ` on which the numerator
vanishes (for `x` close to `z`).  Consequently, for `x` in a small ball around `z`,

`fiberPot R j V x = -(1/π) ∫_{w ∈ D} Φ x w`,

with `D = ball 0 R \ ball (z j) (3δ/4)` a *fixed* domain on which both the numerator and the kernel
are smooth and uniformly bounded.  Differentiation under the integral sign (`ParametricIntegral`)
gives differentiability and the explicit derivative, and evaluating the latter at the two vectors
`Pi.single j 1` and `Pi.single j I` exhibits the relation `L (i e_j) = i · L (e_j)` (because
`x ↦ (w - x_j)⁻¹` is complex differentiable in `x_j`), which forces the `∂̄_j`-combination to vanish.
-/

namespace Work.NN.Core

open MeasureTheory Set

noncomputable section

/-- The continuous linear map `x ↦ Function.update x j 0` on `ℂⁿ`. -/
noncomputable def updateZeroCLM {n : ℕ} (j : Fin n) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  (ContinuousLinearMap.id ℝ (Fin n → ℂ)) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).smulRight
      (Pi.single j (1 : ℂ))

/-- The `j`-th coordinate functional on `ℂⁿ`. -/
noncomputable def projCLM {n : ℕ} (j : Fin n) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j

lemma updateZeroCLM_apply {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    updateZeroCLM j x = Function.update x j 0 := by
  ext l
  simp only [updateZeroCLM, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply]
  rcases eq_or_ne l j with rfl | hl
  · simp
  · simp [Function.update_of_ne hl, Pi.single_eq_of_ne hl]

lemma updateZeroCLM_norm_apply_le {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    ‖updateZeroCLM j x‖ ≤ ‖x‖ := by
  rw [updateZeroCLM_apply, pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro l
  rcases eq_or_ne l j with rfl | hl
  · simp
  · rw [Function.update_of_ne hl]; exact norm_le_pi_norm x l

lemma norm_updateZeroCLM_le {n : ℕ} (j : Fin n) : ‖updateZeroCLM j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]; exact updateZeroCLM_norm_apply_le j x

lemma norm_projCLM_le {n : ℕ} (j : Fin n) : ‖projCLM j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [projCLM, ContinuousLinearMap.proj_apply, one_mul]
  exact norm_le_pi_norm x j

lemma hasFDerivAt_update {n : ℕ} (j : Fin n) (w : ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun y : Fin n → ℂ => Function.update y j w) (updateZeroCLM j) x := by
  have h : (fun y : Fin n → ℂ => Function.update y j w)
      = fun y => updateZeroCLM j y + Pi.single j w := by
    funext y
    rw [updateZeroCLM_apply]
    ext l
    rcases eq_or_ne l j with rfl | hl
    · simp
    · simp [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt (updateZeroCLM j)).add_const (Pi.single j w)

lemma hasFDerivAt_invComp {n : ℕ} (j : Fin n) (w : ℂ) (x : Fin n → ℂ) (h : w - x j ≠ 0) :
    HasFDerivAt (fun y : Fin n → ℂ => (w - y j)⁻¹)
      (((w - x j)⁻¹ * (w - x j)⁻¹) • projCLM j) x := by
  have hsub : HasFDerivAt (fun y : Fin n → ℂ => w - y j) (-(projCLM j)) x := by
    have h1 : (fun y : Fin n → ℂ => w - y j) = fun y => (-(projCLM j)) y + w := by
      funext y
      simp only [projCLM, neg_apply, ContinuousLinearMap.proj_apply, sub_eq_add_neg]
      rw [add_comm]
    rw [h1]
    exact (ContinuousLinearMap.hasFDerivAt (-(projCLM j))).add_const w
  have hinv : HasFDerivAt (fun u : ℂ => u⁻¹)
      (((ContinuousLinearMap.toSpanSingleton ℂ (-((w - x j)^2)⁻¹) : ℂ →L[ℂ] ℂ)).restrictScalars ℝ)
      (w - x j) := (hasFDerivAt_inv h).restrictScalars ℝ
  have hCLM : (((ContinuousLinearMap.toSpanSingleton ℂ (-((w - x j)^2)⁻¹) : ℂ →L[ℂ] ℂ)).restrictScalars ℝ)
        ∘SL (-(projCLM j)) = (((w - x j)⁻¹ * (w - x j)⁻¹) • projCLM j) := by
    ext y
    show (ContinuousLinearMap.toSpanSingleton ℂ (-((w - x j)^2)⁻¹) : ℂ →L[ℂ] ℂ) ((-(projCLM j)) y)
        = (((w - x j)⁻¹ * (w - x j)⁻¹) • projCLM j) y
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_apply]
    simp only [smul_eq_mul, projCLM, ContinuousLinearMap.proj_apply, neg_apply,
      ContinuousLinearMap.neg_apply]
    rw [show ((w - x j)^2)⁻¹ = (w - x j)⁻¹ * (w - x j)⁻¹ from by rw [← inv_pow, sq]]
    ring
  have hchain := hinv.comp x hsub
  rw [hCLM] at hchain
  exact hchain

/-- The integrand `w ↦ V (x with x_j replaced by w) * (w - x_j)⁻¹` of the fixed-disc potential. -/
noncomputable def fiberIntegrand {n : ℕ} (V : (Fin n → ℂ) → ℂ) (j : Fin n) :
    (Fin n → ℂ) → ℂ → ℂ :=
  fun x w => V (Function.update x j w) * (w - x j)⁻¹

/-- The `x`-derivative of `fiberIntegrand`. -/
noncomputable def fiberIntegrandFDeriv {n : ℕ} (V : (Fin n → ℂ) → ℂ) (j : Fin n) :
    (Fin n → ℂ) → ℂ → (Fin n → ℂ) →L[ℝ] ℂ :=
  fun x w =>
    V (Function.update x j w) • (((w - x j)⁻¹ * (w - x j)⁻¹) • projCLM j)
      + (w - x j)⁻¹ • ((fderiv ℝ V (Function.update x j w)).comp (updateZeroCLM j))

lemma hasFDerivAt_fiberIntegrand {n : ℕ} {V : (Fin n → ℂ) → ℂ} (hV : Differentiable ℝ V)
    (j : Fin n) (x : Fin n → ℂ) (w : ℂ) (hw : w - x j ≠ 0) :
    HasFDerivAt (fun y => fiberIntegrand V j y w) (fiberIntegrandFDeriv V j x w) x := by
  have h1 : HasFDerivAt (fun y : Fin n → ℂ => V (Function.update y j w))
      ((fderiv ℝ V (Function.update x j w)).comp (updateZeroCLM j)) x :=
    (hV.differentiableAt.hasFDerivAt).comp x (hasFDerivAt_update j w x)
  have h2 := hasFDerivAt_invComp j w x hw
  have hp := h1.mul h2
  exact hp

lemma fiberIntegrandFDeriv_single_one {n : ℕ} (V : (Fin n → ℂ) → ℂ) (j : Fin n)
    (x : Fin n → ℂ) (w : ℂ) :
    fiberIntegrandFDeriv V j x w (Pi.single j (1 : ℂ))
      = V (Function.update x j w) * ((w - x j)⁻¹ * (w - x j)⁻¹) := by
  have h0 : Function.update (Pi.single j (1 : ℂ)) j 0 = (0 : Fin n → ℂ) := by
    funext l
    rcases eq_or_ne l j with rfl | hl
    · rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hl, Pi.single_eq_of_ne hl]; rfl
  simp only [fiberIntegrandFDeriv, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, updateZeroCLM_apply, projCLM,
    ContinuousLinearMap.proj_apply, h0, Pi.single_eq_same, ContinuousLinearMap.map_zero,
    mul_zero, add_zero, mul_one]

lemma fiberIntegrandFDeriv_single_I {n : ℕ} (V : (Fin n → ℂ) → ℂ) (j : Fin n)
    (x : Fin n → ℂ) (w : ℂ) :
    fiberIntegrandFDeriv V j x w (Pi.single j (Complex.I : ℂ))
      = Complex.I * (V (Function.update x j w) * ((w - x j)⁻¹ * (w - x j)⁻¹)) := by
  have h0 : Function.update (Pi.single j (Complex.I : ℂ)) j 0 = (0 : Fin n → ℂ) := by
    funext l
    rcases eq_or_ne l j with rfl | hl
    · rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hl, Pi.single_eq_of_ne hl]; rfl
  simp only [fiberIntegrandFDeriv, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, updateZeroCLM_apply, projCLM,
    ContinuousLinearMap.proj_apply, h0, Pi.single_eq_same, ContinuousLinearMap.map_zero,
    mul_zero, add_zero]
  ring

lemma norm_fiberIntegrandFDeriv_le {n : ℕ} (V : (Fin n → ℂ) → ℂ) (j : Fin n)
    (x : Fin n → ℂ) (w : ℂ) {M Cv b : ℝ} (hMnn : 0 ≤ M) (hCnn : 0 ≤ Cv)
    (hM : ‖fderiv ℝ V (Function.update x j w)‖ ≤ M)
    (hC : ‖V (Function.update x j w)‖ ≤ Cv)
    (hbw : 1 ≤ b * ‖w - x j‖) :
    ‖fiberIntegrandFDeriv V j x w‖ ≤ Cv * b^2 + b * M := by
  have hb : 0 ≤ b := by
    by_contra h
    have : b * ‖w - x j‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp h)) (norm_nonneg _)
    linarith
  have hwnorm : ‖(w - x j)⁻¹‖ ≤ b := by
    rw [norm_inv]
    rcases eq_or_ne (w - x j) 0 with h0 | h0
    · rw [h0, norm_zero, inv_zero]; exact hb
    · have hcpos : 0 < ‖w - x j‖ := norm_pos_iff.mpr h0
      have hstep : ‖w - x j‖⁻¹ ≤ b * ‖w - x j‖ * ‖w - x j‖⁻¹ := by
        have := mul_le_mul_of_nonneg_right hbw (inv_nonneg.mpr (norm_nonneg (w - x j)))
        rwa [one_mul] at this
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), mul_one] at hstep
  have hvn : ∀ v0 : Fin n → ℂ, ‖Function.update v0 j 0‖ ≤ ‖v0‖ := fun v0 => by
    rw [← updateZeroCLM_apply j v0]; exact updateZeroCLM_norm_apply_le j v0
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [fiberIntegrandFDeriv, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, updateZeroCLM_apply, projCLM,
    ContinuousLinearMap.proj_apply]
  calc ‖V (Function.update x j w) * (((w - x j)⁻¹ * (w - x j)⁻¹) * v j)
          + (w - x j)⁻¹ * (fderiv ℝ V (Function.update x j w) (Function.update v j 0))‖
      ≤ ‖V (Function.update x j w) * (((w - x j)⁻¹ * (w - x j)⁻¹) * v j)‖
          + ‖(w - x j)⁻¹ * (fderiv ℝ V (Function.update x j w) (Function.update v j 0))‖ :=
        norm_add_le _ _
    _ = ‖V (Function.update x j w)‖ * ‖(w - x j)⁻¹ * (w - x j)⁻¹‖ * ‖v j‖
          + ‖(w - x j)⁻¹‖ * ‖fderiv ℝ V (Function.update x j w) (Function.update v j 0)‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]; ring
    _ ≤ Cv * b^2 * ‖v‖ + b * (M * ‖v‖) := by
        have hcc : ‖(w - x j)⁻¹ * (w - x j)⁻¹‖ ≤ b ^ 2 := by
          rw [norm_mul]; nlinarith [hwnorm, norm_nonneg ((w - x j)⁻¹), hb]
        have hfd : ‖fderiv ℝ V (Function.update x j w) (Function.update v j 0)‖ ≤ M * ‖v‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hM (hvn v) (norm_nonneg _) hMnn)
        apply add_le_add
        · exact mul_le_mul (mul_le_mul hC hcc (norm_nonneg _) hCnn) (norm_le_pi_norm v j)
            (norm_nonneg _) (by positivity)
        · exact mul_le_mul hwnorm hfd (norm_nonneg _) hb
    _ = (Cv * b^2 + b * M) * ‖v‖ := by ring

/-- **The target lemma.**  If the `C¹` data `V` vanish on a neighbourhood of the `j`-slice through
`z` (in the tubular sense of `hvan`), then the fixed-disc potential `fiberPot R j V` is real
differentiable at `z` and its `j`-th `∂̄`-derivative vanishes there. -/
theorem fiberPot_dbarCoord_eq_zero {n : ℕ} (R : ℝ) (hR : 0 < R) (j : Fin n)
    {V : (Fin n → ℂ) → ℂ} (hV : ContDiff ℝ 1 V) {z : Fin n → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ y : Fin n → ℂ, ‖y - z‖ < δ → ∀ w : ℂ, ‖w - y j‖ < δ → V (Function.update y j w) = 0) :
    DifferentiableAt ℝ (Work.NN.Core.fiberPot R j V) z ∧
      Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j V) z = 0 := by
  have hVdiff : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hVcont : Continuous V := hV.continuous
  have hfdc : Continuous (fderiv ℝ V) := hV.continuous_fderiv one_ne_zero
  have hrpos : 0 < δ / 4 := by linarith
  -- The compact set on which all bounds are taken.
  set K : Set (Fin n → ℂ) :=
    (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j p.2) ''
      (Metric.closedBall z (δ / 4) ×ˢ Metric.closedBall (0 : ℂ) R) with hK
  have hKc : IsCompact K := by
    rw [hK]
    exact ((isCompact_closedBall z (δ / 4)).prod (isCompact_closedBall (0 : ℂ) R)).image
      (continuous_fst.update j continuous_snd)
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hfdc.continuousOn
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hVcont.continuousOn
  set M : ℝ := max M₀ 0 with hM
  set Cv : ℝ := max C₀ 0 with hCv
  have hMnn : 0 ≤ M := le_max_right _ _
  have hCvnn : 0 ≤ Cv := le_max_right _ _
  have hMb : ∀ y ∈ K, ‖fderiv ℝ V y‖ ≤ M := fun y hy => le_trans (hM₀ y hy) (le_max_left _ _)
  have hCb : ∀ y ∈ K, ‖V y‖ ≤ Cv := fun y hy => le_trans (hC₀ y hy) (le_max_left _ _)
  -- The fixed domain of integration.
  set D : Set ℂ := Metric.ball (0 : ℂ) R \ Metric.ball (z j) (3 * δ / 4) with hD
  have hDmeas : MeasurableSet D := by rw [hD]; exact measurableSet_ball.diff measurableSet_ball
  set μ : Measure ℂ := volume.restrict D with hμ
  set C0 : ℝ := Cv * (2 / δ) ^ 2 + (2 / δ) * M with hC0
  -- Step 1: `fiberPot` agrees, near `z`, with the integral over the fixed domain `D`.
  have hmain : ∀ x : Fin n → ℂ, ‖x - z‖ < δ / 4 →
      fiberPot R j V x = -(Real.pi : ℂ)⁻¹ * ∫ w, fiberIntegrand V j x w ∂μ := by
    intro x hx
    rw [fiberPot_apply]
    congr 1
    have hf_int : IntegrableOn (fun w => V (Function.update x j w) / (w - x j))
        (Metric.ball (0 : ℂ) R) volume := integrableOn_fiberIntegrand R j hVcont x
    have hzero : ∀ w ∈ Metric.ball (0 : ℂ) R ∩ Metric.ball (z j) (3 * δ / 4),
        V (Function.update x j w) / (w - x j) = 0 := by
      rintro w ⟨hwR, hwz⟩
      rw [Metric.mem_ball, dist_eq_norm] at hwz
      have hxznorm : ‖x j - z j‖ ≤ ‖x - z‖ := by
        have := norm_le_pi_norm (x - z) j
        simpa using this
      have hwx : ‖w - x j‖ < δ := by
        have h2 : w - x j = (w - z j) - (x j - z j) := by ring
        rw [h2]
        calc ‖(w - z j) - (x j - z j)‖ ≤ ‖w - z j‖ + ‖x j - z j‖ := norm_sub_le _ _
          _ ≤ ‖w - z j‖ + ‖x - z‖ := by linarith
          _ < 3 * δ / 4 + δ / 4 := by linarith
          _ = δ := by ring
      have hVw : V (Function.update x j w) = 0 := hvan x (by linarith) w hwx
      rw [hVw, zero_div]
    have hsd := setIntegral_sdiff (μ := volume)
        (f := fun w => V (Function.update x j w) / (w - x j))
        (s := Metric.ball (0 : ℂ) R) (t := Metric.ball (0 : ℂ) R ∩ Metric.ball (z j) (3 * δ / 4))
        (measurableSet_ball.inter measurableSet_ball) hf_int Set.inter_subset_left
    rw [setIntegral_eq_zero_of_forall_eq_zero hzero, sub_zero] at hsd
    have hset : Metric.ball (0 : ℂ) R \ (Metric.ball (0 : ℂ) R ∩ Metric.ball (z j) (3 * δ / 4))
        = D := by
      rw [hD]; ext w; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [hset] at hsd
    rw [← hsd, hμ]
    rfl
  have hF_meas : ∀ᶠ x in nhds z, AEStronglyMeasurable (fiberIntegrand V j x) μ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : Measurable fun w : ℂ => V (Function.update x j w) :=
      (hVcont.comp (continuous_update x j)).measurable
    have h2 : Measurable fun w : ℂ => (w - x j)⁻¹ := (measurable_id.sub measurable_const).inv
    have hm : Measurable (fiberIntegrand V j x) := by
      change Measurable fun w : ℂ => V (Function.update x j w) * (w - x j)⁻¹
      exact h1.mul h2
    exact hm.aestronglyMeasurable
  have hF_int : Integrable (fiberIntegrand V j z) μ := by
    rw [hμ]
    exact (integrableOn_fiberIntegrand R j hVcont z).mono_set Set.diff_subset
  have hF'_meas : AEStronglyMeasurable (fiberIntegrandFDeriv V j z) μ := by
    have h1 : Measurable fun w : ℂ => V (Function.update z j w) :=
      (hVcont.comp (continuous_update z j)).measurable
    have h2 : Measurable fun w : ℂ => (w - z j)⁻¹ := (measurable_id.sub measurable_const).inv
    have h3 : Measurable fun w : ℂ => ((w - z j)⁻¹ * (w - z j)⁻¹) • projCLM j :=
      (h2.mul h2).smul_const (projCLM j)
    have h4 : Measurable fun w : ℂ =>
        V (Function.update z j w) • (((w - z j)⁻¹ * (w - z j)⁻¹) • projCLM j) := h1.smul h3
    have hcL : Continuous fun w : ℂ => fderiv ℝ V (Function.update z j w) :=
      hfdc.comp (continuous_update z j)
    have h5 : Measurable fun w : ℂ =>
        (fderiv ℝ V (Function.update z j w)).comp (updateZeroCLM j) := by
      have hc : Continuous fun w : ℂ =>
          (fderiv ℝ V (Function.update z j w)).comp (updateZeroCLM j) := by fun_prop
      exact hc.measurable
    have h6 : Measurable fun w : ℂ =>
        (w - z j)⁻¹ • ((fderiv ℝ V (Function.update z j w)).comp (updateZeroCLM j)) := h2.smul h5
    have h7 : Measurable (fiberIntegrandFDeriv V j z) := by
      change Measurable fun w : ℂ =>
        V (Function.update z j w) • (((w - z j)⁻¹ * (w - z j)⁻¹) • projCLM j)
        + (w - z j)⁻¹ • ((fderiv ℝ V (Function.update z j w)).comp (updateZeroCLM j))
      exact h4.add h6
    exact h7.aestronglyMeasurable
  have h_bound : ∀ᵐ w ∂μ, ∀ x ∈ Metric.ball z (δ / 4),
      ‖fiberIntegrandFDeriv V j x w‖ ≤ C0 := by
    filter_upwards [ae_restrict_mem hDmeas] with w hwD
    intro x hx
    rw [hD] at hwD
    obtain ⟨hwR, hwz⟩ := hwD
    have hx' : ‖x - z‖ < δ / 4 := by simpa [dist_eq_norm] using hx
    have hwR' : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hwR
    have hwznorm : 3 * δ / 4 ≤ ‖w - z j‖ := by
      show 3 * δ / 4 ≤ ‖w - z j‖
      rw [← dist_eq_norm]; exact not_lt.mp hwz
    have hxznorm : ‖x j - z j‖ ≤ ‖x - z‖ := by
      have := norm_le_pi_norm (x - z) j; simpa using this
    have hwx : δ / 2 ≤ ‖w - x j‖ := by
      have h2 : w - x j = (w - z j) - (x j - z j) := by ring
      rw [h2]
      have h3 : ‖x j - z j‖ < δ / 4 := lt_of_le_of_lt hxznorm hx'
      calc δ / 2 = 3 * δ / 4 - δ / 4 := by ring
        _ ≤ ‖w - z j‖ - ‖x j - z j‖ := by linarith
        _ ≤ ‖(w - z j) - (x j - z j)‖ := by
            have := norm_add_le ((w - z j) - (x j - z j)) (x j - z j)
            rw [sub_add_cancel] at this
            linarith
    have hmemK : Function.update x j w ∈ K := by
      rw [hK]
      exact ⟨(x, w), ⟨Metric.ball_subset_closedBall hx, hwR'⟩, rfl⟩
    have hbw : 1 ≤ (2 / δ) * ‖w - x j‖ := by
      have h1 : (2 / δ) * (δ / 2) ≤ (2 / δ) * ‖w - x j‖ :=
        mul_le_mul_of_nonneg_left hwx (by positivity)
      have h2 : (2 / δ) * (δ / 2) = 1 := by field_simp
      rw [h2] at h1; exact h1
    rw [hC0]
    exact norm_fiberIntegrandFDeriv_le V j x w hMnn hCvnn (hMb _ hmemK) (hCb _ hmemK) hbw
  have h_diff : ∀ᵐ w ∂μ, ∀ x ∈ Metric.ball z (δ / 4),
      HasFDerivAt (fun y => fiberIntegrand V j y w) (fiberIntegrandFDeriv V j x w) x := by
    filter_upwards [ae_restrict_mem hDmeas] with w hwD
    intro x hx
    rw [hD] at hwD
    obtain ⟨hwR, hwz⟩ := hwD
    have hx' : ‖x - z‖ < δ / 4 := by simpa [dist_eq_norm] using hx
    have hwznorm : 3 * δ / 4 ≤ ‖w - z j‖ := by
      show 3 * δ / 4 ≤ ‖w - z j‖
      rw [← dist_eq_norm]; exact not_lt.mp hwz
    have hxznorm : ‖x j - z j‖ ≤ ‖x - z‖ := by
      have := norm_le_pi_norm (x - z) j; simpa using this
    have hwx : δ / 2 ≤ ‖w - x j‖ := by
      have h2 : w - x j = (w - z j) - (x j - z j) := by ring
      rw [h2]
      have h3 : ‖x j - z j‖ < δ / 4 := lt_of_le_of_lt hxznorm hx'
      calc δ / 2 = 3 * δ / 4 - δ / 4 := by ring
        _ ≤ ‖w - z j‖ - ‖x j - z j‖ := by linarith
        _ ≤ ‖(w - z j) - (x j - z j)‖ := by
            have := norm_add_le ((w - z j) - (x j - z j)) (x j - z j)
            rw [sub_add_cancel] at this
            linarith
    have hwxpos : w - x j ≠ 0 := by
      have : 0 < ‖w - x j‖ := lt_of_lt_of_le (by linarith : (0 : ℝ) < δ / 2) hwx
      exact norm_pos_iff.mp this
    exact hasFDerivAt_fiberIntegrand hVdiff j x w hwxpos
  have hbound_int : Integrable (fun _ : ℂ => C0) μ := by
    have hfin : μ Set.univ < ⊤ := by
      rw [hμ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hD]
      exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top
    haveI : IsFiniteMeasure μ := ⟨hfin⟩
    exact integrable_const C0
  have hFderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ)
      (H := Fin n → ℂ) (μ := μ) (F := fiberIntegrand V j) (F' := fiberIntegrandFDeriv V j)
      (bound := fun _ : ℂ => C0) (s := Metric.ball z (δ / 4)) (x₀ := z)
      (Metric.ball_mem_nhds z hrpos) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hHdiff : HasFDerivAt
      (fun x : Fin n → ℂ => -(Real.pi : ℂ)⁻¹ * ∫ w, fiberIntegrand V j x w ∂μ)
      ((-(Real.pi : ℂ)⁻¹) • ∫ w, fiberIntegrandFDeriv V j z w ∂μ) z :=
    hFderiv.const_mul _
  have hHeq : (fiberPot R j V) =ᶠ[nhds z]
      (fun x : Fin n → ℂ => -(Real.pi : ℂ)⁻¹ * ∫ w, fiberIntegrand V j x w ∂μ) := by
    filter_upwards [Metric.ball_mem_nhds z hrpos] with x hx
    exact hmain x (by simpa [dist_eq_norm] using hx)
  refine ⟨(hHdiff.congr_of_eventuallyEq hHeq).differentiableAt, ?_⟩
  have hF'_int : Integrable (fiberIntegrandFDeriv V j z) μ :=
    hbound_int.mono' hF'_meas (h_bound.mono (fun w hw => hw z (Metric.mem_ball_self hrpos)))
  have hfdeq : fderiv ℝ (fiberPot R j V) z
      = ((-(Real.pi : ℂ)⁻¹) • ∫ w, fiberIntegrandFDeriv V j z w ∂μ) := by
    rw [hHeq.fderiv_eq, hHdiff.fderiv]
  have hL1 : (∫ w, fiberIntegrandFDeriv V j z w ∂μ) (Pi.single j (1 : ℂ))
      = ∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ :=
    ContinuousLinearMap.integral_apply hF'_int _
  have hL2 : (∫ w, fiberIntegrandFDeriv V j z w ∂μ) (Pi.single j (Complex.I : ℂ))
      = ∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (Complex.I : ℂ)) ∂μ :=
    ContinuousLinearMap.integral_apply hF'_int _
  have hLI : (∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (Complex.I : ℂ)) ∂μ)
      = Complex.I * (∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ) := by
    rw [show (∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (Complex.I : ℂ)) ∂μ)
          = ∫ w, Complex.I * fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ from by
          apply integral_congr_ae
          filter_upwards with w
          rw [fiberIntegrandFDeriv_single_I, fiberIntegrandFDeriv_single_one]]
    rw [integral_const_mul]
  have key : Complex.I * ((-(Real.pi : ℂ)⁻¹) *
        (Complex.I * (∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ)))
      = - ((-(Real.pi : ℂ)⁻¹) *
        (∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ)) := by
    set A : ℂ := ∫ w, fiberIntegrandFDeriv V j z w (Pi.single j (1 : ℂ)) ∂μ with hAdef
    have h1 : Complex.I * ((-(Real.pi : ℂ)⁻¹) * (Complex.I * A))
        = (Complex.I * Complex.I) * ((-(Real.pi : ℂ)⁻¹) * A) := by ring
    rw [h1, Complex.I_mul_I]; ring
  rw [Work.CR.Flat.dbarCoord]
  rw [hfdeq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul, hL1, hL2, hLI, key]
  ring

end

end Work.NN.Core
