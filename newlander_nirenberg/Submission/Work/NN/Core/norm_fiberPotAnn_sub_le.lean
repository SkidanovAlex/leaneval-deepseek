import Mathlib
import Submission.Work.NN.Core.VanishingDefs

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-- Interpolation inequality: if `0 ≤ v ≤ M` and `0 ≤ α ≤ 1` then
`v ≤ M ^ (1 - α) * v ^ α`.  (This is `v = v ^ (1-α) * v ^ α ≤ M ^ (1-α) * v ^ α`.) -/
private lemma le_rpow_mul_of_le {M v α : ℝ} (hM : 0 ≤ M) (hv : 0 ≤ v) (hvM : v ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : v ≤ M ^ (1 - α) * v ^ α := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0]
    exact mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg le_rfl _)
  · have h : v ^ (1 - α) * v ^ α = v := by
      rw [← Real.rpow_add hvpos]
      have : 1 - α + α = 1 := by ring
      rw [this, Real.rpow_one]
    calc v = v ^ (1 - α) * v ^ α := h.symm
      _ ≤ M ^ (1 - α) * v ^ α :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (le_of_lt hvpos) hvM (sub_nonneg.mpr hα1))
            (Real.rpow_nonneg hv α)

/-- Pointwise bound for the difference of the two integrands of `fiberPotAnn` at `z` and `z'`,
for `w` in the annulus: split off the difference of the data `η` (Hölder bound `K0`) and the
difference of the kernels (Lipschitz bound `Klip`). -/
private lemma ptbound {n : ℕ} {R α : ℝ} (j : Fin n)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrs : ∀ i, r i < s i)
    {l : ℕ} {η : Cn n → ℂ} {A0 K0 Klip : ℝ} (hA0 : 0 ≤ A0) (hK0 : 0 ≤ K0) (hKlip : 0 ≤ Klip)
    (hA : ∀ x ∈ fiberAccess r j R, ‖η x‖ ≤ A0)
    (hK : ∀ x ∈ fiberAccess r j R, ∀ y ∈ fiberAccess r j R, ‖η x - η y‖ ≤ K0 * ‖x - y‖ ^ α)
    (hLip : ∀ w ∈ fiberAnnulus (s j) R, ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
        ‖((w - a)⁻¹) ^ (l + 1) - ((w - b)⁻¹) ^ (l + 1)‖ ≤ Klip * ‖a - b‖)
    {z z' : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r)
    (hz' : z' ∈ Work.CR.Flat.polydisc (0 : Cn n) r)
    {w : ℂ} (hw : w ∈ fiberAnnulus (s j) R) :
    ‖η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
        - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1)‖
      ≤ (K0 * (s j - r j)⁻¹ ^ (l + 1) + A0 * Klip * (2 * ‖r‖) ^ (1 - α)) * ‖z - z'‖ ^ α := by
  have hd0 : 0 < s j - r j := sub_pos.mpr (hrs j)
  have hwR : ‖w‖ < R := hw.2
  have huz : Function.update z j w ∈ fiberAccess r j R := mem_fiberAccess_update hz hwR
  have huz' : Function.update z' j w ∈ fiberAccess r j R := mem_fiberAccess_update hz' hwR
  have hzj : ‖z j‖ ≤ r j := le_of_lt (by simpa using hz j)
  have hz'j : ‖z' j‖ ≤ r j := le_of_lt (by simpa using hz' j)
  have hKz : ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (s j - r j)⁻¹ ^ (l + 1) :=
    norm_pow_inv_le_of_mem_fiberAnnulus hd0 l hw (by linarith)
  have hfirst : ‖(η (Function.update z j w) - η (Function.update z' j w))
      * ((w - z j)⁻¹) ^ (l + 1)‖ ≤ K0 * ‖z - z'‖ ^ α * (s j - r j)⁻¹ ^ (l + 1) := by
    rw [norm_mul]
    have hh : ‖η (Function.update z j w) - η (Function.update z' j w)‖ ≤ K0 * ‖z - z'‖ ^ α := by
      refine (hK _ huz _ huz').trans ?_
      have hupd : ‖Function.update z j w - Function.update z' j w‖ ≤ ‖z - z'‖ :=
        norm_update_sub_update_le_van j w z z'
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hupd hα0) hK0
    calc ‖η (Function.update z j w) - η (Function.update z' j w)‖ * ‖((w - z j)⁻¹) ^ (l + 1)‖
        ≤ (K0 * ‖z - z'‖ ^ α) * (s j - r j)⁻¹ ^ (l + 1) :=
          mul_le_mul hh hKz (norm_nonneg _) (mul_nonneg hK0 (Real.rpow_nonneg (norm_nonneg _) α))
      _ = K0 * ‖z - z'‖ ^ α * (s j - r j)⁻¹ ^ (l + 1) := by ring
  have hdelta : ‖z j - z' j‖ ≤ ‖z - z'‖ := by
    simpa using norm_le_pi_norm (z - z') j
  have hz_norm : ‖z‖ ≤ ‖r‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg r)]
    intro i
    have h1 : ‖z i‖ ≤ r i := le_of_lt (by simpa using hz i)
    have h2 : r i ≤ ‖r‖ := by
      have := norm_le_pi_norm r i
      rwa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr i))] at this
    linarith
  have hz'_norm : ‖z'‖ ≤ ‖r‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg r)]
    intro i
    have h1 : ‖z' i‖ ≤ r i := le_of_lt (by simpa using hz' i)
    have h2 : r i ≤ ‖r‖ := by
      have := norm_le_pi_norm r i
      rwa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr i))] at this
    linarith
  have hvM : ‖z - z'‖ ≤ 2 * ‖r‖ := by
    calc ‖z - z'‖ ≤ ‖z‖ + ‖z'‖ := norm_sub_le z z'
      _ ≤ ‖r‖ + ‖r‖ := add_le_add hz_norm hz'_norm
      _ = 2 * ‖r‖ := by ring
  have hM0 : 0 ≤ 2 * ‖r‖ := by positivity
  have hinterp : ‖z - z'‖ ≤ (2 * ‖r‖) ^ (1 - α) * ‖z - z'‖ ^ α :=
    le_rpow_mul_of_le hM0 (norm_nonneg _) hvM hα0 hα1
  have hsecond : ‖η (Function.update z' j w)
      * (((w - z j)⁻¹) ^ (l + 1) - ((w - z' j)⁻¹) ^ (l + 1))‖
      ≤ A0 * Klip * (2 * ‖r‖) ^ (1 - α) * ‖z - z'‖ ^ α := by
    rw [norm_mul]
    have hlip := hLip w hw (z j) (z' j) hzj hz'j
    have hA' : ‖η (Function.update z' j w)‖ ≤ A0 := hA _ huz'
    calc ‖η (Function.update z' j w)‖
          * ‖((w - z j)⁻¹) ^ (l + 1) - ((w - z' j)⁻¹) ^ (l + 1)‖
        ≤ A0 * (Klip * ‖z j - z' j‖) := mul_le_mul hA' hlip (norm_nonneg _) hA0
      _ ≤ A0 * (Klip * ((2 * ‖r‖) ^ (1 - α) * ‖z - z'‖ ^ α)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hdelta.trans hinterp) hKlip) hA0
      _ = A0 * Klip * (2 * ‖r‖) ^ (1 - α) * ‖z - z'‖ ^ α := by ring
  have hdecomp : η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
      - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1)
      = (η (Function.update z j w) - η (Function.update z' j w)) * ((w - z j)⁻¹) ^ (l + 1)
        + η (Function.update z' j w)
            * (((w - z j)⁻¹) ^ (l + 1) - ((w - z' j)⁻¹) ^ (l + 1)) := by ring
  rw [hdecomp]
  calc ‖(η (Function.update z j w) - η (Function.update z' j w)) * ((w - z j)⁻¹) ^ (l + 1)
        + η (Function.update z' j w)
            * (((w - z j)⁻¹) ^ (l + 1) - ((w - z' j)⁻¹) ^ (l + 1))‖
      ≤ ‖(η (Function.update z j w) - η (Function.update z' j w))
            * ((w - z j)⁻¹) ^ (l + 1)‖
          + ‖η (Function.update z' j w)
            * (((w - z j)⁻¹) ^ (l + 1) - ((w - z' j)⁻¹) ^ (l + 1))‖ := norm_add_le _ _
    _ ≤ K0 * ‖z - z'‖ ^ α * (s j - r j)⁻¹ ^ (l + 1)
          + A0 * Klip * (2 * ‖r‖) ^ (1 - α) * ‖z - z'‖ ^ α := add_le_add hfirst hsecond
    _ = (K0 * (s j - r j)⁻¹ ^ (l + 1) + A0 * Klip * (2 * ‖r‖) ^ (1 - α)) * ‖z - z'‖ ^ α := by ring

/-- The integrand of `fiberPotAnn` over the annulus is integrable: the pole `z j` lies inside the
inner disc of the annulus, so the kernel is bounded there. -/
private lemma integrableOn_fiberPotAnn {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n)
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {l : ℕ} {η : Cn n → ℂ} (hη : Continuous η)
    {A0 : ℝ} (hA0 : 0 ≤ A0) (hA : ∀ x ∈ fiberAccess r j R, ‖η x‖ ≤ A0)
    {z : Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    IntegrableOn (fun w : ℂ => η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      (fiberAnnulus (s j) R) := by
  have hmeas : AEStronglyMeasurable
      (fun w : ℂ => η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      (volume.restrict (fiberAnnulus (s j) R)) :=
    (((hη.comp (continuous_update z j)).measurable.mul
      (((measurable_id.sub_const (z j)).inv).pow_const (l + 1)))).aestronglyMeasurable
  refine IntegrableOn.of_bound (volume_fiberAnnulus_lt_top (s j) R) hmeas
    (A0 * (s j - r j)⁻¹ ^ (l + 1)) ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_fiberAnnulus (s j) R)] with w hw
  rw [norm_mul]
  have hd0 : 0 < s j - r j := sub_pos.mpr (hrs j)
  have hzj : ‖z j‖ ≤ r j := le_of_lt (by simpa using hz j)
  have hKz : ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (s j - r j)⁻¹ ^ (l + 1) :=
    norm_pow_inv_le_of_mem_fiberAnnulus hd0 l hw (by linarith)
  have hA' : ‖η (Function.update z j w)‖ ≤ A0 := hA _ (mem_fiberAccess_update hz hw.2)
  exact mul_le_mul hA' hKz (norm_nonneg _) hA0

theorem norm_fiberPotAnn_sub_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {l : ℕ} {η : Work.NN.Core.Cn n → ℂ} (hη : Continuous η) {A0 K0 Klip : ℝ} (hA0 : 0 ≤ A0)
    (hK0 : 0 ≤ K0) (hKlip : 0 ≤ Klip)
    (hA : ∀ x ∈ Work.NN.Core.fiberAccess r j R, ‖η x‖ ≤ A0)
    (hK : ∀ x ∈ Work.NN.Core.fiberAccess r j R, ∀ y ∈ Work.NN.Core.fiberAccess r j R,
        ‖η x - η y‖ ≤ K0 * ‖x - y‖ ^ α)
    (hLip : ∀ w ∈ Work.NN.Core.fiberAnnulus (s j) R, ∀ a b : ℂ, ‖a‖ ≤ r j → ‖b‖ ≤ r j →
        ‖((w - a)⁻¹) ^ (l + 1) - ((w - b)⁻¹) ^ (l + 1)‖ ≤ Klip * ‖a - b‖)
    {z z' : Work.NN.Core.Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) r)
    (hz' : z' ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) r) :
    ‖Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η z
        - Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η z'‖
      ≤ R ^ 2 * (Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0)
        * ‖z - z'‖ ^ α := by
  have hcovol : volume (fiberAnnulus (s j) R) < ⊤ := volume_fiberAnnulus_lt_top (s j) R
  have hintz : IntegrableOn (fun w : ℂ => η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      (fiberAnnulus (s j) R) := integrableOn_fiberPotAnn hR j hr hrs hη hA0 hA hz
  have hintz' : IntegrableOn (fun w : ℂ => η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))
      (fiberAnnulus (s j) R) := integrableOn_fiberPotAnn hR j hr hrs hη hA0 hA hz'
  have hIsub : (∫ w in fiberAnnulus (s j) R, η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      - (∫ w in fiberAnnulus (s j) R, η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))
      = ∫ w in fiberAnnulus (s j) R, (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
          - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1)) :=
    (integral_sub hintz hintz').symm
  have hfp : fiberPotAnn j l (fiberAnnulus (s j) R) η z
        - fiberPotAnn j l (fiberAnnulus (s j) R) η z'
      = -((Real.pi : ℂ))⁻¹ * ∫ w in fiberAnnulus (s j) R,
          (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
            - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1)) := by
    rw [fiberPotAnn_apply, fiberPotAnn_apply, ← hIsub]; ring
  have hnorm : ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z
        - fiberPotAnn j l (fiberAnnulus (s j) R) η z'‖
      = Real.pi⁻¹ * ‖∫ w in fiberAnnulus (s j) R,
          (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
            - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))‖ := by
    rw [hfp, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  set C : ℝ := K0 * (s j - r j)⁻¹ ^ (l + 1) + A0 * Klip * (2 * ‖r‖) ^ (1 - α) with hCdef
  have hpt : ∀ᵐ w ∂(volume.restrict (fiberAnnulus (s j) R)),
      ‖η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
        - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1)‖ ≤ C * ‖z - z'‖ ^ α := by
    filter_upwards [self_mem_ae_restrict (measurableSet_fiberAnnulus (s j) R)] with w hw
    rw [hCdef]
    exact ptbound j hα0 hα1 hr hrs hA0 hK0 hKlip hA hK hLip hz hz' hw
  have hIbound : ‖∫ w in fiberAnnulus (s j) R,
        (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
          - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))‖
      ≤ (C * ‖z - z'‖ ^ α) * (volume (fiberAnnulus (s j) R)).toReal := by
    haveI : IsFiniteMeasure (volume.restrict (fiberAnnulus (s j) R)) :=
      isFiniteMeasure_restrict.mpr (ne_of_lt hcovol)
    have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (fiberAnnulus (s j) R))
      (f := fun w : ℂ => η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
          - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))
      (C := C * ‖z - z'‖ ^ α) hpt
    simp only [Measure.real, Measure.restrict_apply_univ] at h
    exact h
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    refine add_nonneg (mul_nonneg hK0 ?_) (mul_nonneg (mul_nonneg hA0 hKlip) ?_)
    · exact pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt (hrs j)))) _
    · exact Real.rpow_nonneg (by positivity) _
  have hcoordvol : (volume (fiberAnnulus (s j) R)).toReal ≤ R ^ 2 * Real.pi :=
    volume_fiberAnnulus_toReal_le hR.le
  calc ‖fiberPotAnn j l (fiberAnnulus (s j) R) η z
        - fiberPotAnn j l (fiberAnnulus (s j) R) η z'‖
      = Real.pi⁻¹ * ‖∫ w in fiberAnnulus (s j) R,
          (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
            - η (Function.update z' j w) * ((w - z' j)⁻¹) ^ (l + 1))‖ := hnorm
    _ ≤ Real.pi⁻¹ * ((C * ‖z - z'‖ ^ α) * (volume (fiberAnnulus (s j) R)).toReal) :=
        mul_le_mul_of_nonneg_left hIbound (by positivity)
    _ ≤ Real.pi⁻¹ * ((C * ‖z - z'‖ ^ α) * (R ^ 2 * Real.pi)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hcoordvol
          (mul_nonneg hCnn (Real.rpow_nonneg (norm_nonneg _) α))
    _ = R ^ 2 * C * ‖z - z'‖ ^ α := by
        rw [show Real.pi⁻¹ * ((C * ‖z - z'‖ ^ α) * (R ^ 2 * Real.pi))
              = (R ^ 2 * C * ‖z - z'‖ ^ α) * (Real.pi⁻¹ * Real.pi) by ring]
        rw [inv_mul_cancel₀ Real.pi_ne_zero, mul_one]
    _ ≤ R ^ 2 * (Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0)
          * ‖z - z'‖ ^ α := by
        have hM0 : 0 ≤ (2 * ‖r‖) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
        have hD0 : 0 ≤ (s j - r j)⁻¹ ^ (l + 1) :=
          pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt (hrs j)))) _
        have hCle : C ≤ (Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0) := by
          rw [hCdef]
          nlinarith [hK0, hA0, hKlip, hM0, hD0,
            mul_nonneg (mul_nonneg hKlip hM0) hK0, mul_nonneg hD0 hA0]
        have h1 : R ^ 2 * C
            ≤ R ^ 2 * (Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0) := by
          calc R ^ 2 * C
              ≤ R ^ 2 * ((Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0)) :=
                mul_le_mul_of_nonneg_left hCle (sq_nonneg R)
            _ = R ^ 2 * (Klip * (2 * ‖r‖) ^ (1 - α) + (s j - r j)⁻¹ ^ (l + 1)) * (A0 + K0) := by
                ring
        exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg _) α)

end Work.NN.Core
