import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.MuStepA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## Step B — integration in `θ` -/

/-- Measurability of the `ℝ≥0∞`-valued radial weight `muWHat`. -/
lemma mu_measurable_wHat : Measurable muWHat := by
  unfold muWHat
  exact ENNReal.measurable_ofReal.comp (mu_measurable_w.pow_const 2)

/-- **Step B.**  `muMHat F ≤ 3 · muNHat δ ε X`. -/
theorem mu_MHat_le {F X : ℝ → ℝ → ℝ} {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hdom : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ θ ∈ Iθ,
      |F z θ| ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
        (∫ s in Iθ, KJ ε θ s * |X (Real.exp t) s|))
    (hFhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * σθ θ) Iθ)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    muMHat F ≤ 3 * muNHat δ ε X := by
  change (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)))
    ≤ 3 * (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
  have hpt := mu_pointwise hδ hδ2 hε hε2 hdom hXhon hXmeas
  have hstep : (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)))
      ≤ ∫⁻ z in Iz, muWHat z * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with z hz
    refine mul_le_mul' le_rfl ?_
    calc (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ))
        ≤ ∫⁻ θ in Iθ, 3 * (muSigHat θ * muQHat δ ε X z θ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hz]
            with θ hθ
          calc ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)
              ≤ 3 * muSigHat θ * muQHat δ ε X z θ := hθ
            _ = 3 * (muSigHat θ * muQHat δ ε X z θ) := by ring
      _ = 3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ) :=
          MeasureTheory.lintegral_const_mul' 3 _ mu_three_ne_top
  have hstep2 : (∫⁻ z in Iz, muWHat z
        * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)))
      = 3 * ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ) := by
    rw [show (∫⁻ z in Iz, muWHat z
          * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)))
        = ∫⁻ z in Iz, 3 * (muWHat z
            * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)) from
      lintegral_congr (fun z => by ring)]
    exact MeasureTheory.lintegral_const_mul' _ _ mu_three_ne_top
  exact hstep.trans (le_of_eq hstep2)

/-! ## The radial slice bound -/

/-- `z ↦ w(z)² sKer δ (log z - t)` is integrable on `(0,∞)`. -/
lemma mu_integrableOn_wsKer {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t))
      (Set.Ioi 0) := by
  rw [← MeasureTheory.integrable_comp_exp
    (fun z : ℝ => (Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t))]
  have hker : Integrable (fun x : ℝ => sKer δ (x - t)) volume :=
    (Work.FTS.EllSol.EllPkgAux.lj_sKer_integrable hδ).comp_sub_right t
  refine Integrable.mono' (hker.const_mul (5 * ljOm t)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Real.continuous_exp.measurable.smul ?_
    exact ((mu_measurable_w.comp Real.continuous_exp.measurable).pow_const 2).mul
      ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
        ((Real.measurable_log.comp Real.continuous_exp.measurable).sub measurable_const))
  · filter_upwards with x
    have hx : (Real.exp x • ((Work.Spaces.w (Real.exp x)) ^ 2
          * sKer δ (Real.log (Real.exp x) - t)))
        = Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2 * sKer δ (x - t)) := by
      rw [smul_eq_mul, Real.log_exp]
    rw [hx, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos x).le
      (mul_nonneg (sq_nonneg _) (sKer_nonneg hδ _)))]
    by_cases hcomp : |x - t| ≤ 1 / 2
    · have hc := Work.FTS.EllSol.EllPkgAux.wExpCmp x t hcomp
      calc Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2 * sKer δ (x - t))
          = (Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2) * sKer δ (x - t) := by ring
        _ ≤ (5 * ljOm t) * sKer δ (x - t) := by
            refine mul_le_mul_of_nonneg_right ?_ (sKer_nonneg hδ _)
            rw [ljOm]
            linarith [hc]
    · have hz : sKer δ (x - t) = 0 := sKer_eq_zero_of_le_abs hδ (by
        have h : 1 / 2 < |x - t| := not_le.mp hcomp
        linarith [hδ2])
      rw [hz]
      simpa only [mul_zero] using le_refl (0 : ℝ)

/-- The radial slice bound in `ℝ≥0∞`: `∫⁻_z w² k δ z t ≤ ofReal (5 Ω t)`. -/
lemma mu_lintegral_wsKer_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    (∫⁻ z in Iz, muWHat z * muKHat δ z t) ≤ ENNReal.ofReal (5 * ljOm t) := by
  rw [mu_Ioi]
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), muWHat z * muKHat δ z t)
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
    have hfun : (fun z : ℝ => muWHat z * muKHat δ z t)
        = fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
      funext z
      exact muWHat_mul_muKHat δ z t
    rw [hfun]
  rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (mu_integrableOn_wsKer hδ hδ2 t)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z _ => mul_nonneg (sq_nonneg _) (sKer_nonneg hδ _)))]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa only [ljOm, Real.log_exp] using
    Work.FTS.ClassC.UopGenAux.wsq_sKer_log_integral_le (δ := δ) (y := Real.exp t)
      hδ hδ2 (Real.exp_pos t)

/-! ## The change of variables `z = e^t` -/

/-- **The change of variables.**  The `Ω`-weighted `t`-integral of the slice functional of `X`
equals `ofReal` of the `w²`-weighted `z`-integral. -/
lemma mu_expChange (X : ℝ → ℝ → ℝ)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXint : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) Iz) :
    (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) := by
  have hMmnn : ∀ t : ℝ, 0 ≤ MmV X t := fun t =>
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs)))
  have hIoi : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) (Set.Ioi (0 : ℝ)) := by
    change MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) (volume.restrict Iz) at hXint
    rw [mu_Ioi] at hXint
    exact hXint
  have hφ : Integrable (fun t : ℝ => ljOm t * MmV X t) volume := by
    have h := (MeasureTheory.integrable_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))).mpr hIoi
    refine h.congr (Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul, ljOm, MmV]
    ring
  have hR : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 *
        (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))
      = ∫ t : ℝ, ljOm t * MmV X t := by
    rw [← MeasureTheory.integral_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))]
    refine integral_congr_ae (Eventually.of_forall (fun s => ?_))
    simp only [smul_eq_mul, ljOm, MmV]
    ring
  have hIz : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))
      = ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  calc (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t : ℝ, ENNReal.ofReal (ljOm t) * ENNReal.ofReal (MmV X t) :=
        lintegral_congr (fun t => by rw [mu_VsHat_eq hXhon t])
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (ljOm t * MmV X t) :=
        lintegral_congr (fun t => by rw [ENNReal.ofReal_mul (ljOm_nonneg t)])
    _ = ENNReal.ofReal (∫ t : ℝ, ljOm t * MmV X t) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ
          (Eventually.of_forall (fun t => mul_nonneg (ljOm_nonneg t) (hMmnn t)))).symm
    _ = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) := by rw [hIz, hR]

/-! ## Step C — the `z`-integration and the radial Schur step -/

/-- **Step C.**  `muNHat δ ε X` is bounded by `ofReal (5 K₁)` times the `Ω`-weighted `t`-integral
of the slice functional of `X`. -/
theorem mu_NHat_le {X : ℝ → ℝ → ℝ} {δ ε K₁ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε : 0 < ε)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)))
    (hK₁pos : 0 < K₁)
    (hSchur : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u) :
    muNHat δ ε X ≤ ENNReal.ofReal (5 * K₁)
      * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
  change (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
    ≤ ENNReal.ofReal (5 * K₁)
      * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
  have hVs_aesm : AEMeasurable (fun t : ℝ => ∫⁻ s in Iθ, muXsHat X t s * muSigHat s) volume :=
    ((mu_aemeasurable_XsHat hXmeas).mul (mu_aemeasurable_sigHat.comp_snd)).lintegral_prod_right'
  have hVs_ne : ∀ t : ℝ, (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) ≠ ⊤ := fun t => by
    rw [mu_VsHat_eq hXhon t]
    exact ENNReal.ofReal_ne_top
  have hStep1 : (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
      ≤ ∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))) := by
    refine lintegral_mono (fun z => ?_)
    exact mul_le_mul' le_rfl (mu_schurSwap hε hK₁pos.le hXmeas hSchur z)
  have hStep2 : (∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))))
      = ENNReal.ofReal K₁ * ∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
    rw [show (∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))))
        = ∫⁻ z in Iz, ENNReal.ofReal K₁ * (muWHat z * (∫⁻ t, muKHat δ z t
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))) from
      lintegral_congr (fun z => by ring)]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hpull : (∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)))
      = ∫⁻ z in Iz, ∫⁻ t, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
    refine lintegral_congr (fun z => ?_)
    exact (MeasureTheory.lintegral_const_mul' (muWHat z) _
      ENNReal.ofReal_ne_top).symm.trans (lintegral_congr (fun t => by ring))
  have hswap : (∫⁻ z in Iz, ∫⁻ t, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t, ∫⁻ z in Iz, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    MeasureTheory.lintegral_lintegral_swap (μ := volume.restrict Iz) (ν := volume)
      (f := fun z t : ℝ =>
        (muWHat z * muKHat δ z t) * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      (((mu_measurable_wHat.comp measurable_fst).aemeasurable.mul
        (mu_measurable_kHat' δ).aemeasurable).mul (hVs_aesm.comp_snd))
  have hsplit : (∫⁻ t, ∫⁻ z in Iz, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t, (∫⁻ z in Iz, muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    lintegral_congr (fun t => MeasureTheory.lintegral_mul_const' _ _ (hVs_ne t))
  have hStep3 : (∫⁻ t, (∫⁻ z in Iz, muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      ≤ ∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
    refine lintegral_mono (fun t => ?_)
    exact mul_le_mul' (mu_lintegral_wsKer_le hδ hδ2 t) le_rfl
  have hZE : (∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)))
      ≤ ∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    (hpull.trans (hswap.trans hsplit)).le.trans hStep3
  have hW : ENNReal.ofReal K₁ * (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ENNReal.ofReal (5 * K₁) * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
    have hA : (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
        = ENNReal.ofReal 5 * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
      rw [show (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
          = ∫⁻ t, ENNReal.ofReal 5 * (ENNReal.ofReal (ljOm t)
              * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) from
        lintegral_congr (fun t => by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), mul_assoc])]
      exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 5)
        (fun t : ℝ => ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) ENNReal.ofReal_ne_top
    have h5comm : ENNReal.ofReal K₁ * ENNReal.ofReal 5 = ENNReal.ofReal (5 * K₁) :=
      (mul_comm _ _).trans (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)).symm
    rw [hA, ← mul_assoc, h5comm]
  exact (hStep1.trans (le_of_eq hStep2)).trans
    ((mul_le_mul' le_rfl hZE).trans (le_of_eq hW))

end Work.FTS.EllSol.EllPkgAux.MollDom
