import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.LocUnif.DiffQuotFacts
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_pointwise_le
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_measure_null

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A version of `diffQuot_backward_lintegral_le` with only almost-everywhere smoothness in `θ`
(module `Submission.Work.FTS.StrongEps.LocUnif.backwardDiffQuot_ioo_ae`; this file supersedes the
identically named declarations of the scratch module `_LZiooFallback`, which is kept only as a
stub.)

`Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le` assumes that the slice
`z ↦ u z θ` is `C¹` for **every** `θ ∈ [c,d]`.  In the application the smoothness is only known
on the open rectangle `(a,b) × (c,d)`, i.e. off the two boundary lines `θ = c`, `θ = d` — which
are Lebesgue-null.  The two lemmas below are the corresponding statements with the hypothesis
weakened to `∀ᵐ θ ∈ [c,d]`; the proofs are the proofs of the original lemmas with
`lintegral_mono` replaced by `lintegral_mono_ae` and the pointwise input restated.
-/

noncomputable section

open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 1000000

/-- A one-dimensional a.e. property lifts to the rectangle, as a property of the second
coordinate. -/
theorem ae_slice_of_ae_restrict {a b c d : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)), P θ) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), P p.2 := by
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc),
    MeasureTheory.ae_iff]
  refine measure_mono_null (t := Set.Icc a b ×ˢ {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ}) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have h1 : p ∈ Set.Icc a b ×ˢ Set.Icc c d := by
      by_contra hc
      exact hp fun hmem => absurd hmem hc
    have h2 : ¬ P p.2 := fun hP => hp fun _ => hP
    exact ⟨h1.1, h1.2, h2⟩
  · have hT : (MeasureTheory.volume : Measure ℝ) {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ} = 0 := by
      have h1 : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ), θ ∈ Set.Icc c d → P θ :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp h
      have h2 := MeasureTheory.ae_iff.mp h1
      rw [show {θ : ℝ | ¬(θ ∈ Set.Icc c d → P θ)} = {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ}
        from by ext θ; exact not_imp] at h2
      exact h2
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hT, mul_zero]

/-- **Pointwise backward-difference-quotient bound** (smoothness hypotheses supplied directly
rather than as a `∀ θ` statement).  This is `diffQuot_pointwise_le` with `hu_sm` and `hθ`
separated, so that the smoothness of the slice at `θ` can be the conclusion of an a.e. argument.
-/
theorem lz_diffQuot_pointwise_le_ioo {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    {θ : ℝ} (hu_sm : ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b)) (hθ : θ ∈ Set.Icc c d)
    {z : ℝ} (hz : z ∈ Set.Icc a' b') :
    ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
        ∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s)) ^ 2 * (w (z - s) θ) ^ 2) := by
  have hz_ab : z ∈ Set.Icc a b := ⟨by linarith [hz.1, haa'], by linarith [hz.2, hb'b]⟩
  have hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1, hah, hz.1], by linarith [hx.2, hb'b, hz.2]⟩
  have hderiv_cont : ContinuousOn (deriv (fun z' => u z' θ)) (Set.Ioo a b) :=
    hu_sm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont : ContinuousOn (fun s => deriv (fun z' => u z' θ) (z - s)) (Set.Ioc 0 h) := by
    have hmap : Set.MapsTo (fun s : ℝ => z - s) (Set.Ioc 0 h) (Set.Ioo a b) :=
      fun s hs => hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hcs : ContinuousOn (fun s : ℝ => z - s) (Set.Ioc 0 h) :=
      (continuous_const.sub continuous_id).continuousOn
    exact hderiv_cont.comp hcs hmap
  have hmeas : AEStronglyMeasurable (fun s => deriv (fun z' => u z' θ) (z - s))
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  have hFTC : ∫ s in (0:ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ :=
    integral_deriv_slice_sub hh.le hsub hu_sm
  have hCS : ENNReal.ofReal ((u z θ - u (z - h) θ)^2)
      ≤ ENNReal.ofReal h *
        ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2) := by
    have h := ofReal_interval_integral_sq_le hh.le
      (fun s => deriv (fun z' => u z' θ) (z - s)) hmeas
    rw [hFTC, sub_zero] at h
    exact h
  have hpb : ∀ s ∈ Set.Ioc 0 h,
      ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        ≤ ENNReal.ofReal C *
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
    intro s hs
    have hs_ab : z - s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [hz.1, hah, hs.2]
      · linarith [hz.2, hb'b, hs.1]
    have habs : |z - (z - s)| ≤ h := by
      rw [show z - (z - s) = s by ring, abs_of_pos hs.1]
      exact hs.2
    have hCw' : (w z θ)^2 ≤ C * (w (z - s) θ)^2 := hCw z hz_ab (z - s) hs_ab θ hθ habs
    have hCpos : 0 ≤ C := by linarith [hC]
    have hg2 : 0 ≤ (deriv (fun z' => u z' θ) (z - s))^2 := sq_nonneg _
    calc ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        = ENNReal.ofReal ((w z θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [hCw', hg2])
      _ = ENNReal.ofReal C *
            ENNReal.ofReal ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          ENNReal.ofReal_mul hCpos
      _ = ENNReal.ofReal C *
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
          rw [mul_comm ((w (z - s) θ)^2) ((deriv (fun z' => u z' θ) (z - s))^2)]
  have hB : ENNReal.ofReal ((w z θ)^2) *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
      ≤ ENNReal.ofReal C *
        (∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)) := by
    have hmono := setLIntegral_mono' (μ := volume) measurableSet_Ioc hpb
    rw [lintegral_const_mul' (ENNReal.ofReal ((w z θ)^2))
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          ENNReal.ofReal_ne_top,
        lintegral_const_mul' (ENNReal.ofReal C)
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2))
          ENNReal.ofReal_ne_top] at hmono
    exact hmono
  have hcore : ENNReal.ofReal (((u z θ - u (z - h) θ)/h)^2)
      = ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹
        * (ENNReal.ofReal h)⁻¹ := by
    rw [show ((u z θ - u (z - h) θ)/h)^2
        = (u z θ - u (z - h) θ)^2 * (h⁻¹)^2 by ring]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ h⁻¹),
        ENNReal.ofReal_inv_of_pos hh]
    ring
  have ht : ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top
  have h1 := mul_le_mul_of_nonneg_right hCS (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h2 := mul_le_mul_of_nonneg_right h1 (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h3 := mul_le_mul_of_nonneg_right h2 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal ((w z θ)^2))
  have h4 := mul_le_mul_of_nonneg_right hB (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  calc ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      = ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2) * ENNReal.ofReal ((w z θ)^2) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ = (ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹
            * (ENNReal.ofReal h)⁻¹) * ENNReal.ofReal ((w z θ)^2) := by rw [hcore]
    _ ≤ (ENNReal.ofReal h *
            (∫⁻ s in Set.Ioc 0 h,
              ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
          * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2) := h3
    _ = ENNReal.ofReal ((w z θ)^2) *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          * (ENNReal.ofReal h)⁻¹ := by
        rw [show (ENNReal.ofReal h *
              (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
              * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2)
            = (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
              * (ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹) * (ENNReal.ofReal h)⁻¹
              * ENNReal.ofReal ((w z θ)^2) from by ring]
        rw [ht]; ring
    _ ≤ (ENNReal.ofReal C *
          (∫⁻ s in Set.Ioc 0 h,
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)))
          * (ENNReal.ofReal h)⁻¹ := h4
    _ = ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
          ∫⁻ s in Set.Ioc 0 h,
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
        ring

/-- **The backward difference-quotient bound**, with only a.e. smoothness in `θ`. -/
theorem lz_diffQuot_backward_lintegral_le_ioo {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
      ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2) := by
  set G : ℝ × ℝ → ENNReal :=
    fun q => ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) with hGdef
  have hGmeas : AEMeasurable G (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hmeas
  obtain ⟨G', hG'meas, hG'ae⟩ := hGmeas
  have hcne : ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hh).ne')
  -- The a.e. smoothness of the slice, lifted to the inner rectangle.
  have hae_sm : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      ContDiffOn ℝ 1 (fun z => u z p.2) (Set.Ioo a b) :=
    ae_slice_of_ae_restrict (a := a') (b := b') hu_sm
  have hae_sm_v : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      p ∈ Set.Icc a' b' ×ˢ Set.Icc c d → ContDiffOn ℝ 1 (fun z => u z p.2) (Set.Ioo a b) :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).mp hae_sm
  have hstep1 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := by
    rw [← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ =>
            ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)),
        ← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)),
        ← lintegral_const_mul' _ _ hcne]
    refine lintegral_mono_ae ?_
    filter_upwards [hae_sm_v] with p hp
    by_cases hpp : p ∈ Set.Icc a' b' ×ˢ Set.Icc c d
    · rw [Set.indicator_of_mem hpp, Set.indicator_of_mem hpp]
      exact lz_diffQuot_pointwise_le_ioo haa' hb'b hh hah hC hw hCw (hp hpp) hpp.2 hpp.1
    · rw [Set.indicator_of_notMem hpp, Set.indicator_of_notMem hpp, mul_zero]
  have hstep2 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)
      = ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) :=
    lintegral_congr_ae (ae_lintegral_shift_eq haa' hb'b hh hah hG'ae)
  have hstep3 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q :=
    lintegral_lintegral_shift_le haa' hb'b hh hah hG'meas
  have hstep4 : ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q
      = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q :=
    lintegral_congr_ae hG'ae.symm
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := hstep1
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) := by rw [hstep2]
    _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) :=
        mul_le_mul_right hstep3 _
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q) := by rw [hstep4]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q := by
        rw [mul_assoc, ← mul_assoc (ENNReal.ofReal h)⁻¹,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) := rfl

end Work.FTS.StrongEps.LocUnif
