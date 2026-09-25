/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness of the annulus potential `fiberPotAnn`

The potential

  `fiberPotAnn j l (fiberAnnulus (s j) R) η z`
    `= -(1/π) ∫_{w : s j ≤ ‖w‖ ∧ ‖w‖ < R} η (z with z j := w) (w - z j)^{-(l+1)} dw`

is `C^m` on the polydisc `polydisc 0 r` (with `r < s < R` componentwise) whenever `η` is `C^m`.
The point is that on `polydisc 0 r` the pole `z j` stays at distance at least `s j - r j > 0` from
the annulus of integration, so the kernel is a *smooth* (indeed analytic) function of `(z, w)` there
and every derivative may be taken under the integral sign.

The proof is an induction on `m`.  The base case `m = 0` is `continuousOn_fiberPotAnn`.  For the
induction step we use the finite-dimensional characterisation
`contDiffOn_succ_of_fderiv_apply` of `C^{m+1}` functions (all directional derivatives of the
Fréchet derivative are `C^m`) together with the differentiation formula
`fderiv_fiberPotAnn_apply`:
`∂_v (fiberPotAnn j l A η) = fiberPotAnn j l A (∂_v η) + (l+1)(v j) fiberPotAnn j (l+1) A η`.
The differentiability ingredient used by that characterisation is supplied, for `C^1` data, by the
dominated convergence theorem for parametric integrals.
-/
import Mathlib
import Submission.Work.NN.Core.VanishingDefs
import Submission.Work.NN.Core.continuousOn_fiberPotAnn
import Submission.Work.NN.Core.fderiv_fiberPotAnn_apply
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

/-! ## A uniform bound for the insertion map over the annulus -/

/-- Uniform bounds for a continuous datum `η` and its derivative on the set of points obtained by
inserting an annulus point into the `j`-th coordinate of a point of the polydisc `polydisc 0 s`.
All the constants involved may be taken nonnegative. -/
private lemma exists_bound_update_fiberAnnulus {n : ℕ} {j : Fin n} {R : ℝ} {s : Fin n → ℝ}
    {η : (Fin n → ℂ) → ℂ} (hηc : Continuous η) (hηdc : Continuous (fderiv ℝ η)) :
    ∃ M M' : ℝ, 0 ≤ M ∧ 0 ≤ M' ∧
      ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) s, ∀ w ∈ fiberAnnulus (s j) R,
        ‖η (Function.update z j w)‖ ≤ M ∧ ‖fderiv ℝ η (Function.update z j w)‖ ≤ M' := by
  set Rb : ℝ := (∑ i, s i) + R + 1 with hRb
  have hmem : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) s,
      ∀ w ∈ fiberAnnulus (s j) R,
      Function.update z j w ∈ Metric.closedBall (0 : Fin n → ℂ) Rb := by
    intro z hz w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz' : ‖z‖ ≤ ∑ i, ‖z i‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
      exact fun i => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ i)
    have hzw : ‖Function.update z j w‖ ≤ ‖z‖ + ‖w‖ := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rcases eq_or_ne i j with rfl | hi
      · rw [Function.update_self]
        exact le_add_of_nonneg_left (norm_nonneg z)
      · rw [Function.update_of_ne hi]
        exact le_trans (norm_le_pi_norm z i) (le_add_of_nonneg_right (norm_nonneg w))
    have h1 : ‖z‖ < ∑ i, s i :=
      lt_of_le_of_lt hz' (Finset.sum_lt_sum (fun i _ => le_of_lt (by simpa using hz i))
        ⟨j, Finset.mem_univ j, by simpa using hz j⟩)
    have h2 : ‖w‖ < R := hw.2
    refine le_of_lt ?_
    calc ‖Function.update z j w‖ ≤ ‖z‖ + ‖w‖ := hzw
      _ < (∑ i, s i) + R := by linarith
      _ < Rb := by rw [hRb]; linarith
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Fin n → ℂ) Rb).exists_bound_of_continuousOn
    hηc.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Fin n → ℂ) Rb).exists_bound_of_continuousOn
    hηdc.continuousOn
  exact ⟨max M0 0, max M1 0, le_max_right _ _, le_max_right _ _,
    fun z hz w hw => ⟨le_trans (hM0 _ (hmem z hz w hw)) (le_max_left _ _),
      le_trans (hM1 _ (hmem z hz w hw)) (le_max_left _ _)⟩⟩

/-! ## The integrand of the annulus potential and its derivative -/

/-- The integrand of the annulus potential. -/
private def fpaIntegrand {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)

/-- The derivative of the integrand with respect to the base point. -/
private def fpaDeriv {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  (η (Function.update z j w)) • (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))
    + (((w - z j)⁻¹) ^ (l + 1)) • ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))

private lemma measurable_fpaDeriv {n : ℕ} {j : Fin n} {l : ℕ} {η : (Fin n → ℂ) → ℂ}
    (hη : ContDiff ℝ 1 η) (z : Fin n → ℂ) :
    Measurable fun w : ℂ => fpaDeriv j l η z w := by
  have hcont_fderiv : Continuous fun w : ℂ => fderiv ℝ η (Function.update z j w) :=
    (hη.continuous_fderiv one_ne_zero).comp (continuous_update z j)
  have hηz : Measurable fun w : ℂ => η (Function.update z j w) :=
    hη.continuous.measurable.comp (continuous_update z j).measurable
  have hsc : Measurable fun w : ℂ =>
      ((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2) : ℂ) :=
    measurable_const.mul (((measurable_id.sub measurable_const).inv).pow_const (l + 2))
  have hk1m : Measurable fun w : ℂ => (((w - z j)⁻¹) ^ (l + 1) : ℂ) :=
    ((measurable_id.sub measurable_const).inv).pow_const (l + 1)
  have hLmeas : Measurable fun w : ℂ => (fderiv ℝ η (Function.update z j w)).comp (updateZero j) :=
    (continuous_comp_updateZero j).measurable.comp hcont_fderiv.measurable
  simp only [fpaDeriv]
  exact (hηz.smul (hsc.smul (measurable_const : Measurable fun _ : ℂ => coordCLM j))).add
    (hk1m.smul hLmeas)

/-- Pointwise derivative of the integrand: for `w ≠ z j` the map
`y ↦ η (y with y j := w) * (w - y j)^{-(l+1)}` has derivative `fpaDeriv` at `z`. -/
private lemma hasFDerivAt_fpaIntegrand {n : ℕ} {j : Fin n} {l : ℕ} {η : (Fin n → ℂ) → ℂ}
    (hη : ContDiff ℝ 1 η) (w : ℂ) (z : Fin n → ℂ) (hw : w ≠ z j) :
    HasFDerivAt (fun y : Fin n → ℂ => fpaIntegrand j l η y w) (fpaDeriv j l η z w) z := by
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have h1 : HasFDerivAt (fun y : Fin n → ℂ => η (Function.update y j w))
      ((fderiv ℝ η (Function.update z j w)).comp (updateZero j)) z :=
    (hηd.differentiableAt.hasFDerivAt).comp z (hasFDerivAt_update_ann j w z)
  have h2 := hasFDerivAt_inv_pow_update j l w hw (x := z)
  have h3 := h1.mul h2
  have hfe : (fun y : Fin n → ℂ => fpaIntegrand j l η y w)
      = fun y => η (Function.update y j w) * ((w - y j)⁻¹) ^ (l + 1) := rfl
  rw [hfe]
  have hfe' : (fun y : Fin n → ℂ => η (Function.update y j w) * ((w - y j)⁻¹) ^ (l + 1))
      =ᶠ[𝓝 z] ((fun y : Fin n → ℂ => η (Function.update y j w)) *
        fun y => ((w - y j)⁻¹) ^ (l + 1)) :=
    Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]
  have h4 := (hfe'.hasFDerivAt_iff).mpr h3
  simpa only [fpaDeriv] using h4

/-! ## Differentiability of the annulus potential for `C^1` data -/

/-- For `C^1` data `η` the annulus potential is differentiable at every point of `polydisc 0 r`.
This is the differentiation under the integral sign step; the value of the derivative is not
needed. -/
private theorem differentiableAt_fiberPotAnn_of_contDiff_one {n : ℕ} {j : Fin n} {l : ℕ} {R : ℝ}
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : (Fin n → ℂ) → ℂ} (hη : ContDiff ℝ 1 η) {z : Fin n → ℂ}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) :
    DifferentiableAt ℝ (fiberPotAnn j l (fiberAnnulus (s j) R) η) z := by
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) r).mem_nhds hz)
  have hdpos : 0 < s j - r j := by linarith [hr j, hrs j]
  obtain ⟨M, M', hM0, hM0', hb⟩ :=
    exists_bound_update_fiberAnnulus (j := j) (R := R) (s := s) hη.continuous
      (hη.continuous_fderiv one_ne_zero)
  set A : Set ℂ := fiberAnnulus (s j) R with hA
  have hAmeas : MeasurableSet A := measurableSet_fiberAnnulus (s j) R
  have hAfin : volume A < ⊤ := volume_fiberAnnulus_lt_top (s j) R
  haveI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict_of_lt_top hAfin
  -- the pole stays a positive distance `s j - r j` away from the annulus
  have hsep : ∀ x ∈ Metric.ball z δ, ∀ w ∈ A, s j - r j ≤ ‖w - x j‖ := by
    intro x hx w hw
    have hxj : ‖x j‖ < r j := by
      have hx' : x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r := hδsub hx
      simpa using hx' j
    have h1 : s j ≤ ‖w‖ := hw.1
    calc s j - r j ≤ ‖w‖ - ‖x j‖ := by linarith
      _ ≤ ‖w - x j‖ := norm_sub_norm_le w (x j)
  -- the uniform bound on the derivative of the integrand
  set C : ℝ := M * ‖(l + 1 : ℂ)‖ * (s j - r j)⁻¹ ^ (l + 2)
    + M' * (s j - r j)⁻¹ ^ (l + 1) with hCdef
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun w => fpaIntegrand j l η x w)
      (volume.restrict A) := by
    refine Eventually.of_forall fun x => ?_
    simp only [fpaIntegrand]
    exact ((hη.continuous.measurable.comp (continuous_update x j).measurable).mul
      (((measurable_id.sub measurable_const).inv).pow_const (l + 1))).aestronglyMeasurable
  have hzpols : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) s := by
    intro i
    exact lt_trans (by simpa using hz i) (hrs i)
  have hF_int : Integrable (fun w => fpaIntegrand j l η z w) (volume.restrict A) := by
    refine MeasureTheory.Integrable.of_bound ?_ (M * (s j - r j)⁻¹ ^ (l + 1)) ?_
    · simp only [fpaIntegrand]
      exact ((hη.continuous.measurable.comp (continuous_update z j).measurable).mul
        (((measurable_id.sub measurable_const).inv).pow_const (l + 1))).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict hAmeas] with w hw
      simp only [fpaIntegrand]
      have hk : ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (s j - r j)⁻¹ ^ (l + 1) := by
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        rw [norm_inv]
        exact inv_anti₀ hdpos (hsep z (Metric.mem_ball_self hδpos) w hw)
      calc ‖η (Function.update z j w) * (w - z j)⁻¹ ^ (l + 1)‖
          = ‖η (Function.update z j w)‖ * ‖(w - z j)⁻¹ ^ (l + 1)‖ := norm_mul _ _
        _ ≤ M * (s j - r j)⁻¹ ^ (l + 1) :=
            mul_le_mul (hb z hzpols w hw).1 hk (norm_nonneg _) hM0
  have h_bound : ∀ᵐ w ∂(volume.restrict A), ∀ x ∈ Metric.ball z δ,
      ‖fpaDeriv j l η x w‖ ≤ (fun _ : ℂ => C) w := by
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw x hx
    have hxpols : x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) s := by
      intro i
      have hx' : x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r := hδsub hx
      exact lt_trans (by simpa using hx' i) (hrs i)
    obtain ⟨hbx, hbx'⟩ := hb x hxpols w hw
    have hd1 : ‖((w - x j)⁻¹) ^ (l + 1)‖ ≤ (s j - r j)⁻¹ ^ (l + 1) := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      rw [norm_inv]
      exact inv_anti₀ hdpos (hsep x hx w hw)
    have hd2 : ‖((w - x j)⁻¹) ^ (l + 2)‖ ≤ (s j - r j)⁻¹ ^ (l + 2) := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      rw [norm_inv]
      exact inv_anti₀ hdpos (hsep x hx w hw)
    have h1 : ‖(η (Function.update x j w)) •
        (((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
        ≤ M * (‖(l + 1 : ℂ)‖ * (s j - r j)⁻¹ ^ (l + 2)) := by
      calc ‖(η (Function.update x j w)) •
            (((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
          ≤ ‖η (Function.update x j w)‖ *
              ‖(((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2)) • (coordCLM j))‖ :=
            norm_smul_clm_le _ _
        _ ≤ M * (‖(l + 1 : ℂ)‖ * (s j - r j)⁻¹ ^ (l + 2)) := by
            refine mul_le_mul hbx ?_ (norm_nonneg _) hM0
            refine le_trans (norm_smul_clm_le _ _) ?_
            refine le_trans (mul_le_mul_of_nonneg_left (norm_coordCLM_le j) (norm_nonneg _)) ?_
            rw [mul_one, norm_mul]
            exact mul_le_mul_of_nonneg_left hd2 (norm_nonneg _)
    have h2 : ‖(((w - x j)⁻¹) ^ (l + 1)) •
        ((fderiv ℝ η (Function.update x j w)).comp (updateZero j))‖
        ≤ M' * (s j - r j)⁻¹ ^ (l + 1) := by
      refine le_trans (norm_smul_clm_le _ _) ?_
      calc ‖((w - x j)⁻¹) ^ (l + 1)‖ *
            ‖(fderiv ℝ η (Function.update x j w)).comp (updateZero j)‖
          ≤ (s j - r j)⁻¹ ^ (l + 1) * M' :=
            mul_le_mul hd1
              (le_trans (ContinuousLinearMap.opNorm_comp_le _ _) (by
                calc ‖fderiv ℝ η (Function.update x j w)‖ * ‖updateZero j‖
                    ≤ M' * 1 := mul_le_mul hbx' (norm_updateZero_le j) (norm_nonneg _) hM0'
                  _ = M' := mul_one M'))
              (norm_nonneg _) (by positivity)
        _ = M' * (s j - r j)⁻¹ ^ (l + 1) := by ring
    simp only [fpaDeriv]
    calc ‖(η (Function.update x j w)) •
            (((l + 1 : ℂ) * ((w - x j)⁻¹) ^ (l + 2)) • (coordCLM j))
          + (((w - x j)⁻¹) ^ (l + 1)) •
            ((fderiv ℝ η (Function.update x j w)).comp (updateZero j))‖
        ≤ M * (‖(l + 1 : ℂ)‖ * (s j - r j)⁻¹ ^ (l + 2))
          + M' * (s j - r j)⁻¹ ^ (l + 1) :=
          (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = C := by rw [hCdef]; ring
  have hboundint : Integrable (fun _ : ℂ => C) (volume.restrict A) :=
    integrableOn_const (C := C) (volume_fiberAnnulus_lt_top (s j) R).ne (by simp)
  have h_diff : ∀ᵐ w ∂(volume.restrict A), ∀ x ∈ Metric.ball z δ,
      HasFDerivAt (fun y => fpaIntegrand j l η y w) (fpaDeriv j l η x w) x := by
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw x hx
    have hxr : ‖x j‖ < r j := by
      have hx' : x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r := hδsub hx
      simpa using hx' j
    have hwne : w ≠ x j := by
      intro h
      have h1 : s j ≤ ‖w‖ := hw.1
      rw [h] at h1
      linarith
    exact hasFDerivAt_fpaIntegrand hη w x hwne
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume.restrict A)
    (F := fun x w => fpaIntegrand j l η x w)
    (F' := fun x w => fpaDeriv j l η x w)
    (x₀ := z) (bound := fun _ : ℂ => C) (s := Metric.ball z δ)
    (Metric.ball_mem_nhds z hδpos) hF_meas hF_int (measurable_fpaDeriv hη z).aestronglyMeasurable
    h_bound hboundint h_diff
  have hpot : fiberPotAnn j l (fiberAnnulus (s j) R) η
      = fun x => -((Real.pi : ℂ))⁻¹ * ∫ w, fpaIntegrand j l η x w ∂(volume.restrict A) := by
    funext x
    rw [fiberPotAnn_apply]
    simp only [fpaIntegrand, hA]
  exact (hmain.const_mul (-((Real.pi : ℂ))⁻¹)).differentiableAt

/-! ## The main induction -/

private theorem fiberPotAnn_contDiffOn_general {n : ℕ} {j : Fin n} {R : ℝ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R) :
    ∀ m : ℕ, ∀ (l : ℕ) (η : (Fin n → ℂ) → ℂ), ContDiff ℝ m η →
      ContDiffOn ℝ m (fiberPotAnn j l (fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) := by
  intro m
  induction m with
  | zero =>
    intro l η hη
    exact contDiffOn_zero.mpr (continuousOn_fiberPotAnn hr hrs hsR η hη.continuous)
  | succ m ih =>
    intro l η hη
    have hcast : ((Nat.succ m : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by
      rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [hcast] at hη
    have h1le : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) + 1 := by simp
    have hη1 : ContDiff ℝ (1 : WithTop ℕ∞) η := hη.of_le h1le
    have hηm : ContDiff ℝ (m : WithTop ℕ∞) η :=
      hη.of_le le_self_add
    have hAmeas : MeasurableSet (fiberAnnulus (s j) R) := measurableSet_fiberAnnulus (s j) R
    have hAfin : volume (fiberAnnulus (s j) R) < ⊤ := volume_fiberAnnulus_lt_top (s j) R
    obtain ⟨M, M', hM0, hM0', hb⟩ :=
      exists_bound_update_fiberAnnulus (j := j) (R := R) (s := s) hη1.continuous
        (hη1.continuous_fderiv one_ne_zero)
    refine contDiffOn_succ_of_fderiv_apply (𝕜 := ℝ) (n := (m : WithTop ℕ∞))
      (f := fiberPotAnn j l (fiberAnnulus (s j) R) η)
      (s := Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) ?_ ?_ ?_
    · intro z hz
      exact (differentiableAt_fiberPotAnn_of_contDiff_one hr hrs hsR hη1 hz).differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · intro y
      have hff : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r,
          fderiv ℝ (fiberPotAnn j l (fiberAnnulus (s j) R) η) x y
          = fiberPotAnn j l (fiberAnnulus (s j) R)
              (fun y' => fderiv ℝ η y' (Function.update y j 0)) x
            + (l + 1) * (y j) * fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η x := by
        intro x hx
        have hxps : x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) s := by
          intro i
          exact lt_trans (by simpa using hx i) (hrs i)
        exact fderiv_fiberPotAnn_apply (hη := hη1) (hA := hAmeas) (hAfin := hAfin)
          (s := Work.CR.Flat.polydisc (0 : Fin n → ℂ) s) (x := x)
          ((Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) s).mem_nhds hxps)
          (d := s j) (M := M) (M' := M') (by linarith [hr j, hrs j]) hM0 hM0'
          (fun w hw => hw.1) (fun z hz => by simpa using hz j)
          (fun z hz w hw => (hb z hz w hw).1) (fun z hz w hw => (hb z hz w hw).2) y
      have hD : ContDiff ℝ (m : WithTop ℕ∞)
          (fun y' => fderiv ℝ η y' (Function.update y j 0)) := by
        have hfd : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ η) :=
          hη.fderiv_right le_rfl
        exact hfd.clm_apply contDiff_const
      have hsum : ContDiffOn ℝ (m : WithTop ℕ∞)
          (fun x => fiberPotAnn j l (fiberAnnulus (s j) R)
              (fun y' => fderiv ℝ η y' (Function.update y j 0)) x
            + (l + 1) * (y j) * fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η x)
          (Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) := by
        refine ContDiffOn.add (ih l _ hD) ?_
        have := (ih (l + 1) η hηm).const_smul ((l + 1) * (y j))
        simpa only [smul_eq_mul, mul_assoc] using this
      refine hsum.congr (fun x hx => ?_)
      rw [fderivWithin_of_isOpen (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) r) hx,
        hff x hx]

/-- **Smoothness of the annulus potential.**  If `η : ℂⁿ → ℂ` is `C^m` then the annulus potential
`fiberPotAnn j l (fiberAnnulus (s j) R) η` is `C^m` on the polydisc `polydisc 0 r`, provided
`0 < r i < s i` for all `i` and `s j < R`. -/
theorem contDiffOn_fiberPotAnn {n : ℕ} {j : Fin n} {l : ℕ} {R : ℝ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R) (m : ℕ) :
    ∀ η : (Fin n → ℂ) → ℂ, ContDiff ℝ m η →
      ContDiffOn ℝ m (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc 0 r) := by
  intro η hη
  exact fiberPotAnn_contDiffOn_general hr hrs hsR m l η hη

end Work.NN.Core
