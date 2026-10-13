import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice
import Submission.Work.FTS.EllipticEst.H2W.Rfun_bound_two
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelLeft
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelRight
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SliceA/lzero1SliceGrowthQuant`

The quantitative two-sided growth bound for an angular slice `u` of class `C²` on `(0, π/2)`:
the size of `u` at any interior point is controlled by the weighted `L²` size
`‖Lzero1 u‖_{L²(sEta)}` of the source together with the two values of `u` at the reference
point `π/4`, times the endpoint function `1/θ + 1/(π/2 - θ)`.

The proof follows the Wronskian-functional route of `H2W/lzeroGrowthSlice` (the
`C²` chain of which is recorded in `H2W/Rfun_bound_two`):

* `D u θ = cos θ (u θ · 2cos 2θ - u' θ sin 2θ)` has `(D u)' = 2 (Lzero1 u) sinθcos²θ`, so its
  oscillation is at most twice the weighted `L¹` mass `M u = ∫ sinθcos²θ |Lzero1 u|` of the
  source;
* `R u θ = u θ / sin 2θ` has `(R u)' = -D u /(cos θ sin²2θ)`, which turns the bound on `D u`
  into the two growth bounds for `R u`;
* the weighted `L¹` mass is bounded by the weighted `L²` mass through Cauchy–Schwarz with the
  companion weight `1/√sEta ≤ 1`;
* the two explicit kernels `1/(cos s sin²2s)` are evaluated against `sin 2θ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SliceA

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst.H2W.LzeroGrowth

/-! ## Elementary preparation -/

theorem holderConjugate_two_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  exact ⟨by norm_num, by norm_num⟩

/-- Almost every point of `Iθ` (for the restricted measure) lies in the open interval. -/
theorem ae_mem_Ioo_restrict_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_restrict_mem measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  simpa only [Work.Spaces.Iθ] using h1

/-- `Lzero1 u` is a.e. strongly measurable on `Iθ` for `u` of class `C²` on `(0, π/2)`. -/
theorem aestronglyMeasurable_Lzero1_c2 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (Work.FTS.EllipticEst.H2W.LzeroGrowthC2.continuousOn_Lzero1 hu).aestronglyMeasurable
      measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  simpa only [Work.Spaces.Iθ] using h1

theorem aestronglyMeasurable_sqrt_sEta :
    AEStronglyMeasurable (fun θ : ℝ => Real.sqrt (Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iθ) := by
  have hc : ContinuousOn (fun θ : ℝ => Real.sqrt (Work.FTS.EllipticEst.sEta θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sqrt.comp_continuousOn
      (fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt)
  have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.sqrt (Work.FTS.EllipticEst.sEta θ))
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hc.aestronglyMeasurable measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  simpa only [Work.Spaces.Iθ] using h1

theorem finiteMeasure_restrict_Iθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Work.Spaces.Iθ,
        Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩

theorem real_univ_restrict_Iθ : (volume.restrict Work.Spaces.Iθ).real univ = Real.pi / 2 := by
  have hvol : (volume.restrict Work.Spaces.Iθ) univ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Work.Spaces.Iθ,
      Real.volume_Icc, sub_zero]
  show ((volume.restrict Work.Spaces.Iθ) univ).toReal = Real.pi / 2
  rw [hvol, ENNReal.toReal_ofReal (by positivity)]

theorem aestronglyMeasurable_inv_sqrt_sEta :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹)
      (volume.restrict Work.Spaces.Iθ) := by
  have hc : ContinuousOn (fun θ : ℝ => (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ContinuousOn.inv₀ ?_ ?_
    · exact Real.continuous_sqrt.comp_continuousOn
        (fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt)
    · intro θ hθ
      exact ne_of_gt (Real.sqrt_pos.mpr
        (lt_of_lt_of_le zero_lt_one (Work.FTS.EllipticEst.H2W.one_le_sEta hθ)))
  have h1 : AEStronglyMeasurable (fun θ : ℝ => (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hc.aestronglyMeasurable measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  simpa only [Work.Spaces.Iθ] using h1

theorem one_le_sqrt_of_one_le {x : ℝ} (h : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  have hx : 0 ≤ x := le_trans zero_le_one h
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- The angular weight `sinθcos²θ` is at most `1` on `Iθ`. -/
theorem sinCos2_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := by have := Real.cos_sq_le_one θ; linarith
  have h4 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Elliptic.sinCos2]
  calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul h2 h3 h4 (by linarith)
    _ = 1 := by ring

/-! ## The weighted `L¹` mass is controlled by the weighted `L²` mass

Cauchy–Schwarz with the companion weight `(√sEta)⁻¹`, which is bounded by `1` on `Iθ`. -/

theorem Mfun_le_two_sqrt {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hG : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
        Work.Spaces.Iθ
      ∧ Work.FTS.EllipticEst.H2W.LzeroGrowth.Mfun u
          ≤ 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  haveI hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := finiteMeasure_restrict_Iθ
  have hG' : Integrable
      (fun θ : ℝ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := hG
  set g : ℝ → ℝ := Work.FTS.EllipticEst.Lzero1 u with hgdef
  have hgint : Integrable (fun θ : ℝ => g θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    simpa only [hgdef] using hG'
  have hg_ae : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ) := by
    simpa only [hgdef] using aestronglyMeasurable_Lzero1_c2 hu
  have hs_ae : AEStronglyMeasurable (fun θ : ℝ => Real.sqrt (Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iθ) := aestronglyMeasurable_sqrt_sEta
  have hgabs_ae : AEStronglyMeasurable (fun θ : ℝ => |g θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using hg_ae.norm
  set F : ℝ → ℝ := fun θ => |g θ| * Real.sqrt (Work.FTS.EllipticEst.sEta θ) with hFdef
  set H : ℝ → ℝ := fun θ => (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹ with hHdef
  have hF_ae : AEStronglyMeasurable F (volume.restrict Work.Spaces.Iθ) := by
    rw [hFdef]; exact hgabs_ae.mul hs_ae
  have hH_ae : AEStronglyMeasurable H (volume.restrict Work.Spaces.Iθ) := by
    rw [hHdef]; exact aestronglyMeasurable_inv_sqrt_sEta
  -- `F` is in `L²`
  have hF_sq : Integrable (fun θ : ℝ => F θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.congr hgint ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hFdef]
    simp only
    rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ), sq_abs]
  have hFmem : MemLp F (2 : ENNReal) (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hF_ae).mpr hF_sq
  have hFmem' : MemLp F (ENNReal.ofReal 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [ENNReal.ofReal_ofNat]; exact hFmem
  -- `H` is in `L²`
  have hH_sq_le : (fun θ : ℝ => H θ ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [ae_mem_Ioo_restrict_Iθ] with θ hθ
    rw [hHdef]
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.H2W.one_le_sEta hθ
    have h2 : 1 ≤ Real.sqrt (Work.FTS.EllipticEst.sEta θ) := one_le_sqrt_of_one_le h1
    have h3 : (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    have h4 : 0 ≤ (Real.sqrt (Work.FTS.EllipticEst.sEta θ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    nlinarith [h3, h4]
  have hH_sq_int : Integrable (fun θ : ℝ => H θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hH_ae.pow 2) (by
      filter_upwards [hH_sq_le] with θ hθ
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  have hHmem : MemLp H (2 : ENNReal) (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hH_ae).mpr hH_sq_int
  have hHmem' : MemLp H (ENNReal.ofReal 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [ENNReal.ofReal_ofNat]; exact hHmem
  -- Hölder
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict Work.Spaces.Iθ) (p := 2) (q := 2) holderConjugate_two_two
    (Filter.Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun θ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    hFmem' hHmem'
  have hFH : (fun θ : ℝ => F θ * H θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => |g θ|) := by
    filter_upwards [ae_mem_Ioo_restrict_Iθ] with θ hθ
    rw [hFdef, hHdef]
    simp only
    have hpos : 0 < Work.FTS.EllipticEst.sEta θ :=
      lt_of_lt_of_le zero_lt_one (Work.FTS.EllipticEst.H2W.one_le_sEta hθ)
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hpos)), mul_one]
  have hF2 : (fun θ : ℝ => F θ ^ (2 : ℝ)) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => g θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.rpow_two, hFdef]
    simp only
    rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ), sq_abs]
  have hH2eq : (fun θ : ℝ => H θ ^ (2 : ℝ)) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => H θ ^ 2) :=
    Filter.Eventually.of_forall fun θ => Real.rpow_two (H θ)
  have hH2le : ∫ θ, H θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ) ≤ Real.pi / 2 := by
    rw [integral_congr_ae hH2eq]
    have h1 : ∫ θ, (1 : ℝ) ∂(volume.restrict Work.Spaces.Iθ) = Real.pi / 2 := by
      rw [MeasureTheory.integral_const, real_univ_restrict_Iθ]
      simp
    rw [← h1]
    exact MeasureTheory.integral_mono_ae hH_sq_int (integrable_const 1) hH_sq_le
  have hsqrtH : (∫ θ, H θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ)) ^ ((1 : ℝ) / 2)
      ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (∫ θ, H θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ))
        ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_le_sqrt hH2le
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hGval : (∫ θ, F θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    integral_congr_ae hF2
  have hmain : ∫ θ in Work.Spaces.Iθ, |g θ|
      ≤ 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    have h1 : ∫ θ in Work.Spaces.Iθ, |g θ|
        = ∫ θ, F θ * H θ ∂(volume.restrict Work.Spaces.Iθ) :=
      (integral_congr_ae hFH).symm
    calc ∫ θ in Work.Spaces.Iθ, |g θ|
        = ∫ θ, F θ * H θ ∂(volume.restrict Work.Spaces.Iθ) := h1
      _ ≤ (∫ θ, F θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ)) ^ ((1 : ℝ) / 2)
            * (∫ θ, H θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ)) ^ ((1 : ℝ) / 2) :=
          hholder
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ, H θ ^ (2 : ℝ) ∂(volume.restrict Work.Spaces.Iθ)) ^ ((1 : ℝ) / 2) := by
          rw [hGval, Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ) * 2 :=
          mul_le_mul_of_nonneg_left hsqrtH (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          ring
  -- integrability of `|g|`
  have hgabs_int : Integrable (fun θ : ℝ => |g θ|) (volume.restrict Work.Spaces.Iθ) := by
    have hdom : Integrable
        (fun θ : ℝ => (g θ ^ 2 * Work.FTS.EllipticEst.sEta θ + H θ ^ 2))
        (volume.restrict Work.Spaces.Iθ) := hgint.add hH_sq_int
    refine Integrable.mono' (hdom.div_const 2) hgabs_ae ?_
    filter_upwards [ae_mem_Ioo_restrict_Iθ] with θ hθ
    rw [Real.norm_eq_abs, abs_abs]
    have hpos : 0 < Work.FTS.EllipticEst.sEta θ :=
      lt_of_lt_of_le zero_lt_one (Work.FTS.EllipticEst.H2W.one_le_sEta hθ)
    have hFHθ : F θ * H θ = |g θ| := by
      rw [hFdef, hHdef]
      simp only
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hpos)), mul_one]
    have hF2θ : F θ ^ 2 = g θ ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [hFdef]
      simp only
      rw [mul_pow, Real.sq_sqrt (le_of_lt hpos), sq_abs]
    have hamgm : 2 * (F θ * H θ) ≤ F θ ^ 2 + H θ ^ 2 := by
      nlinarith [sq_nonneg (F θ - H θ)]
    rw [hFHθ, hF2θ] at hamgm
    linarith
  -- integrability of `sinθcos²θ · |g|` and the `Mfun` bound
  have hpsig_int : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |g θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' hgabs_int
      ((Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.aestronglyMeasurable).mul hgabs_ae)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Work.FTS.EllipticEst.H2W.LzeroGrowth.sinCos2_nonneg hθ), abs_abs]
    calc Work.Elliptic.sinCos2 θ * |g θ| ≤ 1 * |g θ| :=
          mul_le_mul_of_nonneg_right (sinCos2_le_one_of_mem_Iθ hθ) (abs_nonneg _)
      _ = |g θ| := one_mul _
  have hM : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |g θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |g θ| :=
    setIntegral_mono_on hpsig_int hgabs_int measurableSet_Icc (fun θ hθ => by
      calc Work.Elliptic.sinCos2 θ * |g θ| ≤ 1 * |g θ| :=
            mul_le_mul_of_nonneg_right (sinCos2_le_one_of_mem_Iθ hθ) (abs_nonneg _)
        _ = |g θ| := one_mul _)
  have hfinal : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |g θ|
      ≤ 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, g θ ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    le_trans hM hmain
  refine ⟨?_, ?_⟩
  · show Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      (volume.restrict Work.Spaces.Iθ)
    simpa only [hgdef] using hpsig_int
  · rw [Work.FTS.EllipticEst.H2W.LzeroGrowth.Mfun]
    simpa only [hgdef] using hfinal

/-! ## From the two `Rfun` bounds to the quantitative growth of `u` -/

theorem Rfun_mul_sin' {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    LzeroGrowth.Rfun u θ * Real.sin (2 * θ) = u θ := by
  rw [LzeroGrowth.Rfun]
  exact div_mul_cancel₀ _ (ne_of_gt (LzeroGrowth.sin_two_pos hθ))

theorem growthQuant {u : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
        |LzeroGrowth.Rfun u θ|
          ≤ A + B * ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
    (hright : ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |LzeroGrowth.Rfun u θ|
          ≤ A + B * ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have ht : 0 < Real.pi / 2 - θ := by linarith
  have hs2 : 0 < Real.sin (2 * θ) := LzeroGrowth.sin_two_pos hθ
  have hab : |u θ| = |LzeroGrowth.Rfun u θ| * Real.sin (2 * θ) := by
    rw [← Rfun_mul_sin' (u := u) hθ, abs_mul, abs_of_pos hs2]
  have hC0 : 0 ≤ 10 * (A + B) := by linarith
  rcases le_or_gt θ (Real.pi / 4) with hle | hgt
  · -- the left half
    have hθl : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4) := ⟨hθ0, hle⟩
    have hR := hleft θ hθl
    have hK := lzeroGrowthKernelLeft hθl
    have hcoef : |LzeroGrowth.Rfun u θ| ≤ A + B * ((Real.pi ^ 2 / 8) / θ) := by
      have h1 := mul_le_mul_of_nonneg_left hK hB
      linarith
    have hnn : 0 ≤ A + B * ((Real.pi ^ 2 / 8) / θ) := by
      have h1 : 0 ≤ (Real.pi ^ 2 / 8) / θ := div_nonneg (by positivity) hθ0.le
      exact add_nonneg hA (mul_nonneg hB h1)
    have hsle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have hstep : |u θ| ≤ (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ) := by
      rw [hab]
      exact le_trans (mul_le_mul_of_nonneg_right hcoef hs2.le)
        (mul_le_mul_of_nonneg_left hsle hnn)
    have hval : (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ) = 2 * A * θ + B * (Real.pi ^ 2 / 4) := by
      field_simp
      ring
    have hkey : 2 * A * θ + B * (Real.pi ^ 2 / 4) ≤ 10 * (A + B) / θ := by
      rw [le_div_iff₀ hθ0]
      have hL : (2 * A * θ + B * (Real.pi ^ 2 / 4)) * θ
          = 2 * A * θ ^ 2 + B * (Real.pi ^ 2 / 4) * θ := by ring
      rw [hL]
      have hθ2le : θ ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ hθ0.le hle 2
        nlinarith [h, Real.pi_lt_four, Real.pi_pos]
      have h1 : 2 * A * θ ^ 2 ≤ 10 * A := by nlinarith [hθ2le, hA]
      have h2 : B * (Real.pi ^ 2 / 4) * θ ≤ 10 * B := by
        have h3 : (Real.pi ^ 2 / 4) * θ ≤ 10 := by
          nlinarith [hle, Real.pi_lt_four, Real.pi_pos]
        nlinarith [h3, hB]
      linarith
    have hfinal : 2 * A * θ + B * (Real.pi ^ 2 / 4)
        ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
      have h1 : 10 * (A + B) / θ ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        exact le_add_of_nonneg_right (inv_nonneg.mpr ht.le)
      linarith
    calc |u θ| ≤ (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ) := hstep
      _ = 2 * A * θ + B * (Real.pi ^ 2 / 4) := hval
      _ ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hfinal
  · -- the right half
    have hθr : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨hgt.le, hθ2⟩
    have htle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
    have hR := hright θ hθr
    have hK := lzeroGrowthKernelRight hθr
    have hcoef : |LzeroGrowth.Rfun u θ|
        ≤ A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hK hB
      linarith
    have hnn : 0 ≤ A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2) := by
      have h1 : 0 ≤ (Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2 :=
        div_nonneg (by positivity) (sq_nonneg _)
      exact add_nonneg hA (mul_nonneg hB h1)
    have hsle : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
      have h2 : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
      rw [h2, Real.sin_pi_sub]
      exact Real.sin_le (by linarith)
    have hstep : |u θ| ≤ (A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2))
        * (2 * (Real.pi / 2 - θ)) := by
      rw [hab]
      exact le_trans (mul_le_mul_of_nonneg_right hcoef hs2.le)
        (mul_le_mul_of_nonneg_left hsle hnn)
    have hval : (A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2)) * (2 * (Real.pi / 2 - θ))
        = 2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) := by
      have hC : ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2) * (2 * (Real.pi / 2 - θ))
          = (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) := by
        have htne : Real.pi / 2 - θ ≠ 0 := ne_of_gt ht
        field_simp
        ring
      calc (A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2)) * (2 * (Real.pi / 2 - θ))
          = A * (2 * (Real.pi / 2 - θ))
              + B * (((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2) * (2 * (Real.pi / 2 - θ))) := by
            ring
        _ = 2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) := by
            rw [hC]; ring
    have hkey : 2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ)
        ≤ 10 * (A + B) / (Real.pi / 2 - θ) := by
      rw [le_div_iff₀ ht]
      have hD : (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) * (Real.pi / 2 - θ) = Real.pi ^ 3 / 32 := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]
      have hL : (2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ))
            * (Real.pi / 2 - θ)
          = 2 * A * (Real.pi / 2 - θ) ^ 2 + B * (Real.pi ^ 3 / 32) := by
        calc (2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ))
              * (Real.pi / 2 - θ)
            = 2 * A * (Real.pi / 2 - θ) * (Real.pi / 2 - θ)
                + B * ((Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) * (Real.pi / 2 - θ)) := by ring
          _ = 2 * A * (Real.pi / 2 - θ) ^ 2 + B * (Real.pi ^ 3 / 32) := by rw [hD]; ring
      rw [hL]
      have ht2le : (Real.pi / 2 - θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ ht.le htle 2
        nlinarith [h, Real.pi_lt_four, Real.pi_pos]
      have h1 : 2 * A * (Real.pi / 2 - θ) ^ 2 ≤ 10 * A := by nlinarith [ht2le, hA]
      have h2 : B * (Real.pi ^ 3 / 32) ≤ 10 * B := by
        have hπ : Real.pi ^ 3 ≤ 64 := by
          calc Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 :=
                pow_le_pow_left₀ (le_of_lt Real.pi_pos) (le_of_lt Real.pi_lt_four) 3
            _ = 64 := by norm_num
        have hle : Real.pi ^ 3 / 32 ≤ 10 := by linarith
        calc B * (Real.pi ^ 3 / 32) ≤ B * 10 := mul_le_mul_of_nonneg_left hle hB
          _ = 10 * B := by ring
      linarith
    have hfinal : 2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ)
        ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
      have h1 : 10 * (A + B) / (Real.pi / 2 - θ)
          ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        exact le_add_of_nonneg_left (inv_nonneg.mpr hθ0.le)
      linarith
    calc |u θ| ≤ (A + B * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2))
          * (2 * (Real.pi / 2 - θ)) := hstep
      _ = 2 * A * (Real.pi / 2 - θ) + B * (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) := hval
      _ ≤ 10 * (A + B) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hfinal

/-! ## The values of the two functionals at the reference point `π/4` -/

theorem Rfun_pi_div_four (u : ℝ → ℝ) :
    LzeroGrowth.Rfun u (Real.pi / 4) = u (Real.pi / 4) := by
  rw [LzeroGrowth.Rfun, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two,
    div_one]

theorem Dfun_pi_div_four (u : ℝ → ℝ) :
    LzeroGrowth.Dfun u (Real.pi / 4) = -(Real.sqrt 2 / 2) * deriv u (Real.pi / 4) := by
  rw [LzeroGrowth.Dfun, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.cos_pi_div_four]
  ring

/-! ## The quantitative slice growth bound -/

theorem lzero1SliceGrowthQuant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |u θ| ≤ C * (Real.sqrt (∫ τ in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.Lzero1 u τ) ^ 2 * Work.FTS.EllipticEst.sEta τ)
            + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  refine ⟨50, by norm_num, fun u hu hG θ hθ => ?_⟩
  obtain ⟨hMint, hMle⟩ := Mfun_le_two_sqrt hu hG
  obtain ⟨hRleft, hRright⟩ := Work.FTS.EllipticEst.H2W.Rfun_bound_two hu hMint
  have hR4 : LzeroGrowth.Rfun u (Real.pi / 4) = u (Real.pi / 4) := Rfun_pi_div_four u
  have hD4 : LzeroGrowth.Dfun u (Real.pi / 4) = -(Real.sqrt 2 / 2) * deriv u (Real.pi / 4) :=
    Dfun_pi_div_four u
  set G : ℝ := ∫ τ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.Lzero1 u τ) ^ 2 * Work.FTS.EllipticEst.sEta τ with hGdef
  have hsqrtG : 0 ≤ Real.sqrt G := Real.sqrt_nonneg G
  have hB : LzeroGrowth.Bfun u ≤ |deriv u (Real.pi / 4)| + 4 * Real.sqrt G := by
    rw [LzeroGrowth.Bfun, hD4]
    have h1 : |-(Real.sqrt 2 / 2) * deriv u (Real.pi / 4)| ≤ |deriv u (Real.pi / 4)| := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)]
      have h2 : Real.sqrt 2 / 2 ≤ 1 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      exact mul_le_of_le_one_left (abs_nonneg _) h2
    have h3 : LzeroGrowth.Mfun u ≤ 2 * Real.sqrt G := hMle
    linarith
  have hQ := growthQuant (u := u) (A := |u (Real.pi / 4)|) (B := LzeroGrowth.Bfun u)
    (abs_nonneg _) (LzeroGrowth.Bfun_nonneg u)
    (fun θ hθ => by simpa only [hR4] using hRleft θ hθ)
    (fun θ hθ => by simpa only [hR4] using hRright θ hθ) θ hθ
  have hbr : 0 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hθ.1.le) (inv_nonneg.mpr (by linarith [hθ.2]))
  have hB' : |u (Real.pi / 4)| + LzeroGrowth.Bfun u
      ≤ 5 * (Real.sqrt G + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    linarith [hB, hsqrtG, abs_nonneg (u (Real.pi / 4)), abs_nonneg (deriv u (Real.pi / 4))]
  have hgoal : |u θ| ≤ 50 * (Real.sqrt G + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
    calc |u θ| ≤ 10 * (|u (Real.pi / 4)| + LzeroGrowth.Bfun u) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hQ
      _ ≤ 10 * (5 * (Real.sqrt G + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|))
            * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
          refine mul_le_mul_of_nonneg_right ?_ hbr
          exact mul_le_mul_of_nonneg_left hB' (by norm_num)
      _ = 50 * (Real.sqrt G + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
            * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by ring
  simpa only [hGdef] using hgoal

end Work.FTS.EllipticEst.H2W.SliceA
