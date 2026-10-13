/-
# `ZmollTTB2` — the integrability of the dominating functional and the integration by parts.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB1
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c

/-- **Integrability of the dominating functional.** -/
theorem rhs_integrable (G : ℝ → ℝ → ℝ) (hsl : SliceData G)
    (hsqrt : LocallyIntegrable (fun t : ℝ => Real.sqrt (E2s G (Real.exp t))) volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hε0 : 0 < ε) {z θ : ℝ} (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume := by
  have hKδ : ∀ x : ℝ, |sKer δ x| ≤ (δ * sMass)⁻¹ := fun x => by
    rw [abs_of_nonneg (sKer_nonneg hδ0 x)]
    exact Work.FTS.EllSol.K5cAux.sKer_le_inv hδ0 x
  have hKδ0 : (0 : ℝ) ≤ (δ * sMass)⁻¹ := by have := sMass_pos; positivity
  have hC0 : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ := by have := sMass_pos; positivity
  have hpt : ∀ t : ℝ,
      ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ (3 * (ε * sMass)⁻¹) * (Real.sqrt (Real.pi / 2)
            * Real.sqrt (E2s G (Real.exp t))) := by
    intro t
    have h1 : ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ ∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ :=
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
        (fun s : ℝ => KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
    have h2 : (∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖)
        ≤ ∫ s in Iθ, (3 * (ε * sMass)⁻¹)
            * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
      refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        ((hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).abs.const_mul _) ?_
      exact Filter.Eventually.of_forall fun s => by
        show ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
          ≤ (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
        rw [Real.norm_eq_abs, abs_mul, abs_abs,
          abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
        exact mul_le_mul_of_nonneg_right
          (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) (abs_nonneg _)
    have h3 : (∫ s in Iθ, (3 * (ε * sMass)⁻¹)
          * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
        = (3 * (ε * sMass)⁻¹)
          * (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) :=
      MeasureTheory.integral_const_mul _ _
    have hE2 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) = E2s G (Real.exp t) := by
      simp only [E2s, Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have h4 : (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G (Real.exp t)) := by
      have h4a := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
        (h := fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ?_
      · rw [hE2] at h4a
        exact h4a
      · simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta, Work.Spaces.Iθ,
          Work.Spaces.pth] using
          hsl.deriv2_weighted (Real.exp t) (Real.exp_pos t)
    calc ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ ∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ := h1
      _ ≤ ∫ s in Iθ, (3 * (ε * sMass)⁻¹)
            * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := h2
      _ = (3 * (ε * sMass)⁻¹)
            * (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := h3
      _ ≤ (3 * (ε * sMass)⁻¹) * (Real.sqrt (Real.pi / 2)
            * Real.sqrt (E2s G (Real.exp t))) := mul_le_mul_of_nonneg_left h4 hC0
  set Cst : ℝ := (δ * sMass)⁻¹ * ((3 * (ε * sMass)⁻¹) * Real.sqrt (Real.pi / 2)) with hCst
  set g : ℝ → ℝ := (Set.Icc (Real.log z - δ) (Real.log z + δ)).indicator
    (fun t : ℝ => Cst * Real.sqrt (E2s G (Real.exp t))) with hg
  have hgint : Integrable g volume := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact (hsqrt.integrableOn_isCompact isCompact_Icc).const_mul Cst
  have hmem : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume := by
    have hker : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 0)).continuous.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    refine hker.mul ?_
    have hX : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
        Work.FTS.EllipticEst.Q0 := (hsl.sm.pth.pth).continuousOn
    have hKcont : ContinuousOn (fun p : ℝ × ℝ => KJ ε θ p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((continuous_KJ ε).comp (continuous_const.prodMk continuous_snd)).continuousOn
    have hY : ContinuousOn (fun p : ℝ × ℝ =>
        KJ ε θ p.2 * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2|)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine hKcont.mul ?_
      refine ContinuousOn.abs ?_
      have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
        (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
      exact hX.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
    exact aesm_param_Iθ _ hY
  have hle : ∀ᵐ t ∂volume,
      ‖sKer δ (Real.log z - t) *
        ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ ≤ g t := by
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Set.Icc (Real.log z - δ) (Real.log z + δ)
    · rw [hg, Set.indicator_of_mem ht, Real.norm_eq_abs, abs_mul]
      refine le_trans (mul_le_mul (hKδ _) (hpt t) (abs_nonneg _) hKδ0) (le_of_eq ?_)
      rw [hCst]; ring
    · have hzero : sKer δ (Real.log z - t) = 0 := by
        refine sKer_eq_zero_of_le_abs hδ0 ?_
        rw [Set.mem_Icc, not_and_or] at ht
        rcases ht with h | h
        · rw [not_le] at h
          rw [abs_of_pos (by linarith)]
          linarith
        · rw [not_le] at h
          rw [abs_of_neg (by linarith)]
          linarith
      rw [hg, Set.indicator_of_notMem ht, hzero, zero_mul, norm_zero]
  exact Integrable.mono' hgint hmem hle

/-! ## Integration by parts -/

theorem ibp_km {G : ℝ → ℝ → ℝ} (hsl : SliceData G) {ε w θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hw : 0 < w) (hθ : θ ∈ Iθ) :
    (∫ s in Iθ, kmθθ ε θ s * G w s)
      = ∫ s in Iθ, km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hQint : IntegrableOn (fun s : ℝ => G w s) Iθ :=
    (hsl.cont w hw).integrableOn_compact isCompact_Icc
  have hQ''int : IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s) Iθ :=
    hsl.deriv2_int w hw
  obtain ⟨Mq, hMq0, hMq⟩ := hsl.deriv_bdd w hw
  have hQ'aesm : AEStronglyMeasurable (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (volume.restrict Iθ) := aesm_slice_deriv G hsl.sm hw
  obtain ⟨Mk', hMk'0, hMk'⟩ := kms_bdd hε0
  have hpart1 : IntegrableOn (fun s : ℝ => kmθθ ε θ s * G w s) Iθ := by
    have h := hQint.mul_continuousOn (continuous_kmθθ ε θ).continuousOn isCompact_Icc
    exact h.congr_fun (fun s _ => mul_comm _ _) measurableSet_Icc
  have hpart2 : IntegrableOn (fun s : ℝ => kms ε θ s * deriv (fun s' : ℝ => G w s') s) Iθ := by
    refine Integrable.mono' (MeasureTheory.integrableOn_const (s := Iθ) (C := Mk' * Mq) ?_) ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · have hm1 : AEStronglyMeasurable (fun s : ℝ => kms ε θ s) (volume.restrict Iθ) :=
        ((continuous_kms ε θ).aestronglyMeasurable).restrict
      exact AEStronglyMeasurable.mul hm1 hQ'aesm
    · rw [Work.FTS.EllSol.EllPkgAux.restrict_Iθ_eq_restrict_Ioo]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
        show ‖kms ε θ s * deriv (fun s' : ℝ => G w s') s‖ ≤ Mk' * Mq
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hMk' θ s) (hMq s hs) (abs_nonneg _) hMk'0)
  have hpart4 : IntegrableOn (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s)
      Iθ := by
    have h := hQ''int.mul_continuousOn (continuous_km ε θ).continuousOn isCompact_Icc
    exact h.congr_fun (fun s _ => mul_comm _ _) measurableSet_Icc
  have hI1 : IntervalIntegrable (fun s : ℝ => kmθθ ε θ s * G w s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart1)
  have hI2 : IntervalIntegrable
      (fun s : ℝ => kms ε θ s * deriv (fun s' : ℝ => G w s') s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart2)
  have hI4 : IntervalIntegrable
      (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart4)
  -- Step 1: the FTC for `k' * Q`
  have hF1der : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s' : ℝ => kms ε θ s' * G w s')
        (kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s) s :=
    fun s hs => (hasDerivAt_kms_s ε θ s).mul (slice_hasDerivAt G hsl.sm hw hs)
  have hF1int : IntervalIntegrable (fun s : ℝ =>
      kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s)
      volume 0 (Real.pi / 2) := hI1.add hI2
  have ht1a : Tendsto (fun s : ℝ => kms ε θ s * G w s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => kms ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (kms ε θ 0)) :=
      (continuous_kms ε θ).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul (hsl.tr0 w hw)
    simpa using h2
  have ht1b : Tendsto (fun s : ℝ => kms ε θ s * G w s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => kms ε θ s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 (kms ε θ (Real.pi / 2))) :=
      (continuous_kms ε θ).tendsto _ |>.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul (hsl.trpi w hw)
    simpa using h2
  have hFTC1 : (∫ s in (0 : ℝ)..(Real.pi / 2),
      (kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hF1der hF1int ht1a ht1b
    simpa using h
  -- Step 2: the FTC for `k * Q'`
  have hF2der : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s' : ℝ => km ε θ s' * deriv (fun s'' : ℝ => G w s'') s')
        (kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
          + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s) s :=
    fun s hs => (hasDerivAt_km_s ε θ s).mul (slice_hasDerivAt2 G hsl.sm hw hs)
  have hF2int : IntervalIntegrable (fun s : ℝ =>
      kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
        + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s) volume 0 (Real.pi / 2) :=
    hI2.add hI4
  have hkm0 : Tendsto (fun s : ℝ => km ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => km ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (km ε θ 0)) :=
      (continuous_km ε θ).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    rw [km_zero_left' hε0 hε1 hθ] at h1
    exact h1
  have hkmpi : Tendsto (fun s : ℝ => km ε θ s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => km ε θ s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 (km ε θ (Real.pi / 2))) :=
      (continuous_km ε θ).tendsto _ |>.mono_left nhdsWithin_le_nhds
    rw [km_zero_right hε0 hε1 hθ] at h1
    exact h1
  have ht2a : Tendsto (fun s : ℝ => km ε θ s * deriv (fun s'' : ℝ => G w s'') s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    refine tendsto_mul_zero (c := Mq) hkm0 ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with s hs hys
    exact hMq s ⟨hys, hs.2⟩
  have ht2b : Tendsto (fun s : ℝ => km ε θ s * deriv (fun s'' : ℝ => G w s'') s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    refine tendsto_mul_zero (c := Mq) hkmpi ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
        (show Real.pi / 2 < Real.pi by linarith [Real.pi_pos])] with s hs hys
    exact hMq s ⟨hs.1, hys⟩
  have hFTC2 : (∫ s in (0 : ℝ)..(Real.pi / 2),
      (kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
        + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hF2der hF2int ht2a ht2b
    simpa using h
  -- combine
  have hAB : (∫ s in (0 : ℝ)..(Real.pi / 2), kmθθ ε θ s * G w s)
      + (∫ s in (0 : ℝ)..(Real.pi / 2), kms ε θ s * deriv (fun s' : ℝ => G w s') s) = 0 := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    exact hFTC1
  have hBC : (∫ s in (0 : ℝ)..(Real.pi / 2), kms ε θ s * deriv (fun s' : ℝ => G w s') s)
      + (∫ s in (0 : ℝ)..(Real.pi / 2),
          km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s) = 0 := by
    rw [← intervalIntegral.integral_add hI2 hI4]
    exact hFTC2
  have hAC : (∫ s in (0 : ℝ)..(Real.pi / 2), kmθθ ε θ s * G w s)
      = ∫ s in (0 : ℝ)..(Real.pi / 2), km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s := by
    linarith
  rw [← intervalIntegral_Iθ_eq (fun s : ℝ => kmθθ ε θ s * G w s),
    ← intervalIntegral_Iθ_eq (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s)]
  exact hAC

end Work.FTS.EllSol.EllPkgAux.MollDom
