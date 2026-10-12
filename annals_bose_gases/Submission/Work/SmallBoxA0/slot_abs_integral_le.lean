import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

set_option linter.style.haveILetI false

open MeasureTheory Filter
open scoped Real

/--
Absolute-value bound for a triple product over the box: if `F` is (a.e. strongly
measurable and) bounded by `K` and `g`, `H` are continuous, then

  `|∫_{abox} g·F·H| ≤ K · (∫_{abox} g²)^{1/2} · (∫_{abox} H²)^{1/2}`.

Proof: `|∫| ≤ ∫‖·‖`, then `‖g F H‖ ≤ K ‖g‖ ‖H‖` pointwise, and finally
Cauchy–Schwarz (Hölder with `p = q = 2`) for the `L²` functions `g`, `H`.
-/
lemma slot_abs_integral_le {N : ℕ} {s K : ℝ} (hs : 0 < s)
    {F : Submission.BoseGases.X N → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)))
    (hFb : ∀ x, |F x| ≤ K) {g H : Submission.BoseGases.X N → ℝ} (hg : Continuous g) (hH : Continuous H) :
    |∫ x in Submission.BoseGases.abox N s, g x * F x * H x|
      ≤ K * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (g x) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (H x) ^ 2) := by
  -- The restricted box measure is finite.
  haveI hfin : IsFiniteMeasure
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top N s hs.le⟩
  -- `K ≥ 0`, since `|F x| ≤ K` for every point.
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (F (0 : Submission.BoseGases.X N))) (hFb 0)
  -- Continuity on the compact box gives uniform bounds.
  obtain ⟨Cg, hCg⟩ :=
    (Submission.BoseGases.abox_compact N hs).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨CH, hCH⟩ :=
    (Submission.BoseGases.abox_compact N hs).exists_bound_of_continuousOn hH.continuousOn
  have hCg_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)),
      ‖g x‖ ≤ Cg := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N s)]
    filter_upwards with x hx using hCg x hx
  have hCH_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)),
      ‖H x‖ ≤ CH := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N s)]
    filter_upwards with x hx using hCH x hx
  have hCg'_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)),
      ‖g x‖ ≤ max Cg 0 :=
    hCg_ae.mono (fun x h => le_trans h (le_max_left _ _))
  have hCH'_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)),
      ‖H x‖ ≤ max CH 0 :=
    hCH_ae.mono (fun x h => le_trans h (le_max_left _ _))
  -- `g`, `H ∈ L²` on the box.
  have hgm : MemLp g 2 (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)) :=
    MeasureTheory.MemLp.of_bound (p := (2 : ENNReal))
      (hg.aestronglyMeasurable.restrict) Cg hCg_ae
  have hHm : MemLp H 2 (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)) :=
    MeasureTheory.MemLp.of_bound (p := (2 : ENNReal))
      (hH.aestronglyMeasurable.restrict) CH hCH_ae
  -- Cauchy–Schwarz (Hölder with conjugate exponents `2, 2`).
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox N s))
      (f := g) (g := H) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by simpa using hgm) (by simpa using hHm)
  -- Integrability of the two functions compared in the monotonicity step.
  have hprod_int : Integrable (fun x => ‖g x * F x * H x‖)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)) := by
    refine MeasureTheory.Integrable.of_bound ?_ (max Cg 0 * K * max CH 0) ?_
    · exact (((hg.aestronglyMeasurable.restrict).mul hFm).mul
        (hH.aestronglyMeasurable.restrict)).norm
    · filter_upwards [hCg'_ae, hCH'_ae] with x hgx hHx
      have hF' : ‖F x‖ ≤ K := by rw [Real.norm_eq_abs]; exact hFb x
      rw [norm_norm, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hgx hF' (norm_nonneg _) (le_max_right _ _)) hHx (norm_nonneg _)
        (mul_nonneg (le_max_right _ _) hK0)
  have hInt2 : Integrable (fun x => K * (‖g x‖ * ‖H x‖))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N s)) := by
    refine MeasureTheory.Integrable.of_bound ?_ (|K| * (max Cg 0 * max CH 0)) ?_
    · exact ((hg.aestronglyMeasurable.restrict).norm.mul
        (hH.aestronglyMeasurable.restrict).norm).const_mul K
    · filter_upwards [hCg'_ae, hCH'_ae] with x hgx hHx
      have hm : 0 ≤ ‖g x‖ * ‖H x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hgx hHx (norm_nonneg _) (le_max_right _ _))
        (abs_nonneg _)
  -- Step 1: `|∫ gFH| ≤ ∫ ‖gFH‖`.
  have h1 : |∫ x in Submission.BoseGases.abox N s, g x * F x * H x|
      ≤ ∫ x in Submission.BoseGases.abox N s, ‖g x * F x * H x‖ := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox N s))
      (fun x => g x * F x * H x)
    rwa [Real.norm_eq_abs] at h
  -- Step 2: `∫ ‖gFH‖ ≤ ∫ K(‖g‖ ‖H‖)`.
  have h2 : ∫ x in Submission.BoseGases.abox N s, ‖g x * F x * H x‖
      ≤ ∫ x in Submission.BoseGases.abox N s, K * (‖g x‖ * ‖H x‖) := by
    refine MeasureTheory.integral_mono_ae hprod_int hInt2 ?_
    filter_upwards with x
    have hF' : ‖F x‖ ≤ K := by rw [Real.norm_eq_abs]; exact hFb x
    rw [norm_mul, norm_mul]
    calc ‖g x‖ * ‖F x‖ * ‖H x‖ ≤ ‖g x‖ * K * ‖H x‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF' (norm_nonneg _)) le_rfl (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) hK0)
      _ = K * (‖g x‖ * ‖H x‖) := by ring
  -- Step 3: pull the constant `K` out of the integral.
  have h3 : ∫ x in Submission.BoseGases.abox N s, K * (‖g x‖ * ‖H x‖)
      = K * ∫ x in Submission.BoseGases.abox N s, ‖g x‖ * ‖H x‖ := by
    rw [MeasureTheory.integral_const_mul]
  -- Step 4: Cauchy–Schwarz, converted to the `Real.sqrt` normalisations.
  have hCS : ∫ x in Submission.BoseGases.abox N s, ‖g x‖ * ‖H x‖
      ≤ Real.sqrt (∫ x in Submission.BoseGases.abox N s, (g x) ^ 2)
        * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (H x) ^ 2) := by
    have hA : ∫ x in Submission.BoseGases.abox N s, ‖g x‖ ^ (2 : ℝ)
        = ∫ x in Submission.BoseGases.abox N s, g x ^ 2 := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have hB : ∫ x in Submission.BoseGases.abox N s, ‖H x‖ ^ (2 : ℝ)
        = ∫ x in Submission.BoseGases.abox N s, H x ^ 2 := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [hA, hB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
    exact hholder
  calc |∫ x in Submission.BoseGases.abox N s, g x * F x * H x|
      ≤ ∫ x in Submission.BoseGases.abox N s, ‖g x * F x * H x‖ := h1
    _ ≤ ∫ x in Submission.BoseGases.abox N s, K * (‖g x‖ * ‖H x‖) := h2
    _ = K * ∫ x in Submission.BoseGases.abox N s, ‖g x‖ * ‖H x‖ := h3
    _ ≤ K * (Real.sqrt (∫ x in Submission.BoseGases.abox N s, (g x) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (H x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS hK0
    _ = K * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (g x) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox N s, (H x) ^ 2) := by ring

end Work.SmallBoxA0
