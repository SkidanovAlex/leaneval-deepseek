import Submission.FUP.DbarCutoff2
import Submission.Commons.Analysis.Convolution.hasCompactSupport_integral_smul_sub
import Submission.Commons.MeasureTheory.integrable_indicator_prod_norm_sub
import Submission.Commons.Analysis.Convolution.aemeasurable_uncurry_ofReal_mul_enorm_sq

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Convolution of forms with a compactly supported kernel

This module sets up the convolution `z ↦ ∫ y, ρ y • V (z - y)` of a function `V` with values in a
real normed space, and the key identity identifying the pairing of a *test form* `F` against
`ρ * V` with the pairing against the *covariantly shifted* test forms:

  `∫ z, ⟪F z, (ρ * V) z⟫ ∂μ_φ = ∫ y, ρ y • (∫ z, ⟪covShift φ y z • F (z+y), V z⟫ ∂μ_φ) ∂y`.

These are the analytic inputs of the transfer lemmas `dbarWeak2_conv` / `dbarAdjWeak_conv`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- Convolution of a function with values in a real normed space with a real-valued kernel. -/
noncomputable def convFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : FormDu d → ℝ) (V : FormDu d → E) : FormDu d → E :=
  fun z => ∫ y, ρ y • V (z - y) ∂(volume : Measure (FormDu d))

@[simp] lemma convFun_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : FormDu d → ℝ) (V : FormDu d → E) (z : FormDu d) :
    convFun ρ V z = ∫ y, ρ y • V (z - y) ∂(volume : Measure (FormDu d)) := rfl

lemma measurable_sub_left (z : FormDu d) : Measurable (fun y : FormDu d => z - y) :=
  measurable_const.sub measurable_id

lemma measurableEmbedding_sub_left (z : FormDu d) :
    MeasurableEmbedding (fun y : FormDu d => z - y) :=
  MeasurableEquiv.measurableEmbedding
    ((MeasurableEquiv.neg (FormDu d)).trans (MeasurableEquiv.addLeft z))

lemma measurePreserving_sub_left (z : FormDu d) :
    MeasurePreserving (fun y : FormDu d => z - y) (volume : Measure (FormDu d))
      (volume : Measure (FormDu d)) := by
  refine ⟨measurable_sub_left z, ?_⟩
  have hc : (fun y : FormDu d => z - y) = (fun w : FormDu d => w + z) ∘ Neg.neg := by
    funext y; simp only [Function.comp_apply, sub_eq_add_neg]; ring
  rw [hc, ← Measure.map_map (measurable_add_const z) measurable_neg,
    Measure.map_neg_eq_self, map_add_right_eq_self]

/-- **Local integrability of the shifted function.** -/
lemma integrableOn_comp_sub_left {E : Type*} [NormedAddCommGroup E] {V : FormDu d → E}
    (hV : LocallyIntegrable V (volume : Measure (FormDu d))) {K : Set (FormDu d)} (hK : IsCompact K)
    (z : FormDu d) :
    IntegrableOn (fun y => V (z - y)) K (volume : Measure (FormDu d)) := by
  have hpre : (fun y : FormDu d => z - y) ⁻¹' ((fun w : FormDu d => z - w) '' K) = K := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hzw⟩
      rw [sub_right_inj] at hzw
      rw [← hzw]
      exact hw
    · intro hy
      exact ⟨y, hy, rfl⟩
  have h1 := (measurePreserving_sub_left z).integrableOn_comp_preimage
    (measurableEmbedding_sub_left z) (f := V)
    (s := (fun w : FormDu d => z - w) '' K)
  rw [hpre] at h1
  exact h1.mpr (hV.integrableOn_isCompact (hK.image (continuous_const.sub continuous_id)))

/-- **Local integrability of the mollifying integrand.** -/
lemma integrable_smul_sub_of_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : FormDu d → ℝ} {V : FormDu d → E} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ)
    (hV : LocallyIntegrable V (volume : Measure (FormDu d))) (z : FormDu d) :
    Integrable (fun y => ρ y • V (z - y)) (volume : Measure (FormDu d)) := by
  obtain ⟨C, hC⟩ := hρs.exists_bound_of_continuousOn hρc.continuousOn
  have hsub : IntegrableOn (fun y => V (z - y)) (tsupport ρ) (volume : Measure (FormDu d)) :=
    integrableOn_comp_sub_left hV hρs z
  have hsub2 : Integrable ((tsupport ρ).indicator (fun y => ‖V (z - y)‖))
      (volume : Measure (FormDu d)) :=
    (integrable_indicator_iff hρs.isClosed.measurableSet).mpr hsub.norm
  have hg : Integrable (fun y => C * ((tsupport ρ).indicator (fun y => ‖V (z - y)‖) y))
      (volume : Measure (FormDu d)) := hsub2.const_mul C
  have hVasm : AEStronglyMeasurable (fun y : FormDu d => V (z - y))
      (volume : Measure (FormDu d)) := by
    have h2 : AEStronglyMeasurable V
        (Measure.map (fun y : FormDu d => z - y) (volume : Measure (FormDu d))) := by
      rw [(measurePreserving_sub_left z).map_eq]
      exact hV.aestronglyMeasurable
    exact h2.comp_measurable (measurable_sub_left z)
  refine hg.mono' (hρc.aestronglyMeasurable.smul hVasm) ?_
  filter_upwards with y
  by_cases hy : y ∈ tsupport ρ
  · have h1 : ((tsupport ρ).indicator (fun y => ‖V (z - y)‖)) y = ‖V (z - y)‖ :=
      Set.indicator_of_mem hy _
    rw [h1, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _)
  · have h1 : ((tsupport ρ).indicator (fun y => ‖V (z - y)‖)) y = 0 :=
      Set.indicator_of_notMem hy _
    simp only [h1, mul_zero, norm_smul, image_eq_zero_of_notMem_tsupport hy, norm_zero,
      zero_mul, le_refl]

section Pairing

lemma inner_real_smul_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (r : ℝ) : inner ℂ x (r • y) = r • inner ℂ x y := by
  rw [show r • y = (r : ℂ) • y from rfl, inner_smul_right, Complex.real_smul]

lemma inner_real_smul_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (r : ℝ) : inner ℂ (r • x) y = r • inner ℂ x y := by
  rw [show r • x = (r : ℂ) • x from rfl, inner_smul_left, Complex.real_smul]
  simp

/-- The covariant shift factor is real, hence fixed by conjugation. -/
lemma star_covShift (φ : FormDu d → ℝ) (y z : FormDu d) :
    star (covShift φ y z) = covShift φ y z := by
  rw [covShift_apply,
    show (((φ z : ℝ) : ℂ) - ((φ (z + y) : ℝ) : ℂ)) = (((φ z - φ (z + y) : ℝ)) : ℂ) from by
      push_cast; ring,
    ← Complex.ofReal_exp, Complex.star_def, Complex.conj_ofReal]

/-- The pointwise identity relating the ordinary pairing to the covariantly shifted one. -/
lemma inner_covShift_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ : FormDu d → ℝ) (F V : FormDu d → E) (y z : FormDu d) :
    Real.exp (-(φ (z + y))) • inner ℂ (F (z + y)) (V z)
      = Real.exp (-(φ z)) • inner ℂ (covShift φ y z • F (z + y)) (V z) := by
  rw [inner_smul_left, starRingEnd_apply, star_covShift, covShift_apply,
    show (((φ z : ℝ) : ℂ) - ((φ (z + y) : ℝ) : ℂ)) = (((φ z - φ (z + y) : ℝ)) : ℂ) from by
      push_cast; ring,
    ← Complex.ofReal_exp, Complex.real_smul, Complex.real_smul,
    show Real.exp (-φ (z + y)) = Real.exp (-φ z) * Real.exp (φ z - φ (z + y)) from by
      rw [← Real.exp_add]; congr 1; ring]
  push_cast
  ring

/-- **The pairing identity for the convolution.**  Pairing a compactly supported test form `F`
against the convolution `ρ * V` equals the average over `y` of the pairings against the
*covariantly shifted* test forms `z ↦ covShift φ y z • F (z + y)`. -/
theorem inner_convFun_eq {φ : FormDu d → ℝ} (hφ : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : FormDu d → E} {V : FormDu d → E} {ρ : FormDu d → ℝ}
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hV : LocallyIntegrable V (volume : Measure (FormDu d)))
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hInt : Integrable (Function.uncurry fun z y =>
        Real.exp (-(φ z)) • (ρ y • inner ℂ (F z) (V (z - y))))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d)))) :
    ∫ z, inner ℂ (F z) (convFun ρ V z) ∂(wtMeasure φ)
      = ∫ y, ρ y • (∫ z, inner ℂ (covShift φ y z • F (z + y)) (V z) ∂(wtMeasure φ))
          ∂(volume : Measure (FormDu d)) := by
  have hpt : ∀ z, inner ℂ (F z) (convFun ρ V z)
      = ∫ y, ρ y • inner ℂ (F z) (V (z - y)) ∂(volume : Measure (FormDu d)) := by
    intro z
    rw [convFun_apply, ← integral_inner
      (integrable_smul_sub_of_locallyIntegrable hρc hρs hV z) (F z)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    exact inner_real_smul_right (F z) (V (z - y)) (ρ y)
  rw [show (∫ z, inner ℂ (F z) (convFun ρ V z) ∂(wtMeasure φ))
      = ∫ z, (∫ y, ρ y • inner ℂ (F z) (V (z - y)) ∂(volume : Measure (FormDu d)))
          ∂(wtMeasure φ) from integral_congr_ae (Eventually.of_forall hpt)]
  simp only [integral_wtMeasure hφ]
  rw [show (∫ z, Real.exp (-(φ z)) •
        (∫ y, ρ y • inner ℂ (F z) (V (z - y)) ∂(volume : Measure (FormDu d)))
        ∂(volume : Measure (FormDu d)))
      = ∫ z, ∫ y, Real.exp (-(φ z)) • (ρ y • inner ℂ (F z) (V (z - y)))
          ∂(volume : Measure (FormDu d)) ∂(volume : Measure (FormDu d))
      from integral_congr_ae (Eventually.of_forall fun z =>
        (integral_smul (Real.exp (-(φ z)))
          (fun y => ρ y • inner ℂ (F z) (V (z - y)))).symm)]
  rw [integral_integral_swap hInt]
  rw [show (∫ y, ∫ z, Real.exp (-(φ z)) • (ρ y • inner ℂ (F z) (V (z - y)))
        ∂(volume : Measure (FormDu d)) ∂(volume : Measure (FormDu d)))
      = ∫ y, ρ y • (∫ z, Real.exp (-(φ z)) • inner ℂ (F z) (V (z - y))
          ∂(volume : Measure (FormDu d))) ∂(volume : Measure (FormDu d))
      from integral_congr_ae (Eventually.of_forall fun y => by
        dsimp only
        rw [show (fun z => Real.exp (-(φ z)) • (ρ y • inner ℂ (F z) (V (z - y))))
            = fun z => ρ y • (Real.exp (-(φ z)) • inner ℂ (F z) (V (z - y))) from by
          funext z; rw [smul_comm]]
        rw [integral_smul])]
  rw [show (∫ y, ρ y • (∫ z, Real.exp (-(φ z)) • inner ℂ (F z) (V (z - y))
        ∂(volume : Measure (FormDu d))) ∂(volume : Measure (FormDu d)))
      = ∫ y, ρ y • (∫ z, Real.exp (-(φ (z + y))) • inner ℂ (F (z + y)) (V z)
          ∂(volume : Measure (FormDu d))) ∂(volume : Measure (FormDu d))
      from integral_congr_ae (Eventually.of_forall fun y => by
        dsimp only
        congr 1
        rw [← integral_add_right_eq_self
          (fun z => Real.exp (-(φ z)) • inner ℂ (F z) (V (z - y))) y]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [add_sub_cancel_right])]
  rw [show (∫ y, ρ y • (∫ z, Real.exp (-(φ (z + y))) • inner ℂ (F (z + y)) (V z)
        ∂(volume : Measure (FormDu d))) ∂(volume : Measure (FormDu d)))
      = ∫ y, ρ y • (∫ z, Real.exp (-(φ z)) •
          inner ℂ (covShift φ y z • F (z + y)) (V z)
          ∂(volume : Measure (FormDu d))) ∂(volume : Measure (FormDu d))
      from integral_congr_ae (Eventually.of_forall fun y => by
        dsimp only
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        exact inner_covShift_eq φ F V y z)]

/-- **Integrability of the uncurried pairing integrand.** -/
lemma integrable_uncurry_inner_conv {φ : FormDu d → ℝ} (hφ : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : FormDu d → E} {V : FormDu d → E} {ρ : FormDu d → ℝ}
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hV : LocallyIntegrable V (volume : Measure (FormDu d)))
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) :
    Integrable (Function.uncurry fun z y =>
      Real.exp (-(φ z)) • (ρ y • inner ℂ (F z) (V (z - y))))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  obtain ⟨CF, hCF⟩ := hFs.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨Cφ, hCφ⟩ := hFs.exists_bound_of_continuousOn (Real.continuous_exp.comp hφ.neg).continuousOn
  obtain ⟨Cρ, hCρ⟩ := hρs.exists_bound_of_continuousOn hρc.continuousOn
  have hbase : Integrable ((tsupport F ×ˢ tsupport ρ).indicator
      (fun p : FormDu d × FormDu d => ‖V (p.1 - p.2)‖))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    Commons.MeasureTheory.integrable_indicator_prod_norm_sub hV hFs hρs
  have hg := hbase.const_mul (CF * Cφ * Cρ)
  refine hg.mono' ?_ ?_
  · have hq : Measure.QuasiMeasurePreserving (fun p : FormDu d × FormDu d => p.1 - p.2)
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d)))
        (volume : Measure (FormDu d)) :=
      ⟨measurable_fst.sub measurable_snd,
        Commons.Analysis.Convolution.map_sub_prod_absolutelyContinuous (E := FormDu d)⟩
    have hVc : AEStronglyMeasurable (fun p : FormDu d × FormDu d => V (p.1 - p.2))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      hV.aestronglyMeasurable.comp_quasiMeasurePreserving hq
    have hφm : AEStronglyMeasurable (fun p : FormDu d × FormDu d => Real.exp (-(φ p.1)))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      ((hφ.measurable.comp measurable_fst).neg.exp).aestronglyMeasurable
    exact hφm.smul (hρc.aestronglyMeasurable.comp_snd.smul
      (hFc.aestronglyMeasurable.comp_fst.inner hVc))
  · filter_upwards with p
    rcases p with ⟨z, y⟩
    by_cases hz : z ∈ tsupport F
    · by_cases hy : y ∈ tsupport ρ
      · rw [Set.indicator_of_mem (Set.mk_mem_prod hz hy)]
        simp only [Function.uncurry_apply_pair, norm_smul,
          Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
        have h1 : ‖inner ℂ (F z) (V (z - y))‖ ≤ CF * ‖V (z - y)‖ :=
          (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hCF z hz) (norm_nonneg _))
        have h2 : |ρ y| ≤ Cρ := hCρ y hy
        have h3 : Real.exp (-(φ z)) ≤ Cφ := by
          have h := hCφ z hz
          simp only [Function.comp_apply] at h
          rwa [Real.norm_of_nonneg (Real.exp_nonneg _)] at h
        have hCF0 : 0 ≤ CF := le_trans (norm_nonneg _) (hCF z hz)
        have hCρ0 : 0 ≤ Cρ := le_trans (abs_nonneg _) h2
        have hCφ0 : 0 ≤ Cφ := le_trans (Real.exp_nonneg _) h3
        calc Real.exp (-(φ z)) * (|ρ y| * ‖inner ℂ (F z) (V (z - y))‖)
            ≤ Cφ * (Cρ * (CF * ‖V (z - y)‖)) := by gcongr
          _ = (CF * Cφ * Cρ) * ‖V (z - y)‖ := by ring
      · have h1 : ((tsupport F ×ˢ tsupport ρ).indicator
            (fun p : FormDu d × FormDu d => ‖V (p.1 - p.2)‖)) (z, y) = 0 :=
          Set.indicator_of_notMem (fun h => hy h.2) _
        rw [h1, mul_zero]
        simp only [Function.uncurry_apply_pair, image_eq_zero_of_notMem_tsupport hy,
          zero_smul, smul_zero, norm_zero, le_refl]
    · have h1 : ((tsupport F ×ˢ tsupport ρ).indicator
          (fun p : FormDu d × FormDu d => ‖V (p.1 - p.2)‖)) (z, y) = 0 :=
        Set.indicator_of_notMem (fun h => hz h.1) _
      rw [h1, mul_zero]
      simp only [Function.uncurry_apply_pair, image_eq_zero_of_notMem_tsupport hz,
        inner_zero_left, smul_zero, norm_zero, le_refl]

end Pairing

end Submission.FUP
