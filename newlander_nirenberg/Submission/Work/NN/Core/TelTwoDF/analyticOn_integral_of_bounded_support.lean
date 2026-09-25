import Mathlib
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport
import Submission.Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound

/-!
# Real analyticity of an integral with a compactly supported bounded weight

Let `X` be a real normed space, `Ω ⊆ X` and `U ⊆ ℂ` open, and let `K : ℂ → ℂ` be an
a.e. strongly measurable, bounded function with compact support contained in `U`.  If
`F : X × ℂ → ℂ` is real analytic on `Ω × U`, then

`z ↦ ∫ v, K v * F (z, v)`

is real analytic on `Ω`.

The proof follows `analyticOn_integral_disc_tsupport`, but replaces the compact parameter
set `closedBall z₀ ρ × tsupport K` (which need not be compact in an infinite dimensional
`X`) by the compact set `{z₀} × tsupport K`: the only points at which the Taylor expansion
of `F` is used are the points `(z₀, w)` with `w ∈ tsupport K`.  The weight is no longer
assumed continuous; all integrability statements are obtained from boundedness together
with the finiteness of the measure of `tsupport K`.
-/

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Metric Set
open scoped Topology

/-- The inclusion of the first factor of a product has operator norm at most one. -/
private lemma norm_inl_le_one_prod (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖ContinuousLinearMap.inl ℝ E ℂ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [ContinuousLinearMap.inl_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x),
    one_mul]

theorem analyticOn_integral_of_bounded_support {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) {U : Set ℂ} (hU : IsOpen U) {K : ℂ → ℂ}
    (hKm : MeasureTheory.AEStronglyMeasurable K) (hKs : HasCompactSupport K)
    (hKb : ∃ C, ∀ v, ‖K v‖ ≤ C) (hKU : tsupport K ⊆ U)
    {F : X × ℂ → ℂ} (hF : AnalyticOn ℝ F (Ω ×ˢ U)) :
    AnalyticOn ℝ (fun z : X => ∫ v, K v * F (z, v)) Ω := by
  classical
  obtain ⟨CK, hCK⟩ := hKb
  have hCKnn : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0)
  rw [hΩ.analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  -- ## Step 1: the compact parameter set `{z₀} × tsupport K`
  set Kc : Set (X × ℂ) := {z₀} ×ˢ tsupport K with hKcdef
  have hKcc : IsCompact Kc := isCompact_singleton.prod hKs.isCompact
  have hUopen : IsOpen (Ω ×ˢ U) := hΩ.prod hU
  have hKcsub : Kc ⊆ Ω ×ˢ U := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hz₀, hKU hw⟩
  obtain ⟨R, hRpos, C, hCpos, hconv, hbound⟩ :=
    analytic_uniform_taylor_bound hUopen hF hKcc hKcsub
  haveI : IsFiniteMeasure (volume.restrict (tsupport K)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKs.isCompact.measure_lt_top⟩
  -- ## Step 2: the coefficient maps of the candidate power series
  set coef : (k : ℕ) → ℂ → (X [×k]→L[ℝ] ℂ) := fun k w =>
    (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)).compContinuousLinearMap
      (fun _ : Fin k => ContinuousLinearMap.inl ℝ X ℂ) with hcoefdef
  have hcoef_apply : ∀ (k : ℕ) (w : ℂ) (v : Fin k → X),
      coef k w v = ((k.factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ k F (z₀, w) (fun i => (v i, 0)) := by
    intro k w v
    rw [hcoefdef]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inl_apply, smul_apply]
  have hcoef_bound : ∀ (k : ℕ) (w : ℂ), w ∈ tsupport K → ‖coef k w‖ * R ^ k ≤ C := by
    intro k w hw
    have hp : (z₀, w) ∈ Kc := by
      rw [hKcdef]; exact ⟨rfl, hw⟩
    have hb := hbound (z₀, w) hp k
    have hle : ‖coef k w‖ ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)‖ := by
      have hprod : ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ X ℂ‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) (norm_inl_le_one_prod _)
      rw [hcoefdef]
      refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
      calc ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)‖ *
              ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ X ℂ‖
          ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)‖ := mul_one _
    calc ‖coef k w‖ * R ^ k
        ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w)‖ * R ^ k :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hRpos.le k)
      _ ≤ C := hb
  -- ## Step 3: continuity of the coefficient maps in the parameter
  have hiter_cont : ∀ k : ℕ, ContinuousOn (fun w : ℂ => iteratedFDeriv ℝ k F (z₀, w))
      (tsupport K) := by
    intro k w hw
    have hwU : (z₀, w) ∈ Ω ×ˢ U := ⟨hz₀, hKU hw⟩
    have hAnal : AnalyticAt ℝ F (z₀, w) := hF.analyticAt (hUopen.mem_nhds hwU)
    have hcA : ContinuousAt (iteratedFDeriv ℝ k F) (z₀, w) :=
      (hAnal.contDiffAt (n := ⊤)).continuousAt_iteratedFDeriv le_top
    exact hcA.comp_continuousWithinAt
      (continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩).continuousWithinAt
  have hcoef_cont : ∀ k : ℕ, ContinuousOn (fun w : ℂ => coef k w) (tsupport K) := by
    intro k
    have h1 : ContinuousOn (fun w : ℂ => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w))
        (tsupport K) := (hiter_cont k).const_smul ((k.factorial : ℝ)⁻¹)
    have h2 : ContinuousOn (fun w : ℂ =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ X ℂ))
          (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, w))) (tsupport K) :=
      (ContinuousLinearMap.continuous _).comp_continuousOn h1
    convert h2 using 1
    ext w
    rw [hcoefdef, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  -- ## Step 4: the candidate power series
  have hInt : ∀ k : ℕ, IntegrableOn (fun w : ℂ => K w • coef k w) (tsupport K) := by
    intro k
    refine MeasureTheory.Integrable.of_bound ?_ (CK * (C / R ^ k)) ?_
    · exact hKm.restrict.smul
        ((hcoef_cont k).aestronglyMeasurable (isClosed_tsupport K).measurableSet)
    · refine Filter.Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ tsupport K
      · rw [norm_smul]
        have hle : ‖coef k w‖ ≤ C / R ^ k := by
          rw [le_div_iff₀ (pow_pos hRpos k)]
          exact hcoef_bound k w hw
        exact mul_le_mul (hCK w) hle (norm_nonneg _) hCKnn
      · rw [norm_smul, image_eq_zero_of_notMem_tsupport hw, norm_zero, zero_mul]
        exact mul_nonneg hCKnn (div_nonneg hCpos.le (pow_nonneg hRpos.le k))
  have hIθ : IntegrableOn (fun w : ℂ => ‖K w‖) (tsupport K) := by
    refine MeasureTheory.Integrable.of_bound (hKm.restrict.norm) CK ?_
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (norm_nonneg (K w))]
    exact hCK w
  set a : FormalMultilinearSeries ℝ X ℂ :=
    fun k => ∫ w in tsupport K, K w • coef k w with hadef
  have ha_bound : ∀ k : ℕ, ‖a k‖ * R ^ k ≤ (∫ w in tsupport K, ‖K w‖) * C := by
    intro k
    have h1 : ‖a k‖ ≤ ∫ w in tsupport K, ‖K w‖ * ‖coef k w‖ := by
      rw [hadef]
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      simp only [norm_smul]
    have h2 : (∫ w in tsupport K, ‖K w‖ * ‖coef k w‖) * R ^ k
        ≤ (∫ w in tsupport K, ‖K w‖) * C := by
      have hRHS : (∫ w in tsupport K, ‖K w‖) * C = ∫ w in tsupport K, ‖K w‖ * C :=
        (MeasureTheory.integral_mul_const C fun w => ‖K w‖).symm
      rw [hRHS, ← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
      · have hInt2 : IntegrableOn (fun w : ℂ => ‖K w‖ * ‖coef k w‖) (tsupport K) := by
          refine MeasureTheory.Integrable.of_bound ?_ (CK * (C / R ^ k)) ?_
          · exact hKm.restrict.norm.mul
              ((hcoef_cont k).norm.aestronglyMeasurable (isClosed_tsupport K).measurableSet)
          · refine Filter.Eventually.of_forall fun w => ?_
            rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
            by_cases hw : w ∈ tsupport K
            · have hle : ‖coef k w‖ ≤ C / R ^ k := by
                rw [le_div_iff₀ (pow_pos hRpos k)]
                exact hcoef_bound k w hw
              exact mul_le_mul (hCK w) hle (norm_nonneg _) hCKnn
            · rw [image_eq_zero_of_notMem_tsupport hw, norm_zero, zero_mul]
              exact mul_nonneg hCKnn (div_nonneg hCpos.le (pow_nonneg hRpos.le k))
        exact hInt2.mul_const _
      · exact hIθ.mul_const C
      · have hae : ∀ᵐ w ∂(volume.restrict (tsupport K)),
            (‖K w‖ * ‖coef k w‖) * R ^ k ≤ ‖K w‖ * C := by
          rw [MeasureTheory.ae_restrict_iff' (isClosed_tsupport K).measurableSet]
          refine Filter.Eventually.of_forall fun w hw => ?_
          have hb := hcoef_bound k w hw
          calc (‖K w‖ * ‖coef k w‖) * R ^ k = ‖K w‖ * (‖coef k w‖ * R ^ k) := by ring
            _ ≤ ‖K w‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        exact hae
    calc ‖a k‖ * R ^ k
        ≤ (∫ w in tsupport K, ‖K w‖ * ‖coef k w‖) * R ^ k :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hRpos.le k)
      _ ≤ (∫ w in tsupport K, ‖K w‖) * C := h2
  have hle_radius : ((R.toNNReal : NNReal) : ENNReal) ≤ a.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound a
      ((∫ w in tsupport K, ‖K w‖) * C) fun k => ?_
    rw [Real.coe_toNNReal R hRpos.le]
    exact ha_bound k
  -- ## Step 5: the power series sums to the integral
  have hHasSum : ∀ y : X, ‖y‖ < R →
      HasSum (fun k : ℕ => a k (fun _ => y))
        (∫ w, K w • F (z₀ + y, w)) := by
    intro y hy
    have hq0 : 0 ≤ ‖y‖ / R := div_nonneg (norm_nonneg _) hRpos.le
    have hq1 : ‖y‖ / R < 1 := (div_lt_one hRpos).mpr hy
    have hpt : ∀ᵐ w ∂(volume.restrict (tsupport K)),
        HasSum (fun k : ℕ => K w • (coef k w (fun _ => y))) (K w • F (z₀ + y, w)) := by
      refine Filter.Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ tsupport K
      · have hp : (z₀, w) ∈ Kc := by
          rw [hKcdef]; exact ⟨rfl, hw⟩
        have hy' : ‖(y, (0 : ℂ))‖ < R := by
          rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg y)]; exact hy
        have hhs := (hconv (z₀, w) hp (y, 0) hy').const_smul (K w)
        have hEq : (fun i : ℕ => K w • (coef i w (fun _ => y)))
            = fun i : ℕ => K w • ((i.factorial : ℝ)⁻¹ •
                iteratedFDeriv ℝ i F (z₀, w) (fun _ => (y, 0))) := by
          funext i
          rw [hcoef_apply i w (fun _ => y)]
        have hEq2 : (z₀, w) + (y, (0 : ℂ)) = (z₀ + y, w) := by
          simp [Prod.mk_add_mk]
        rw [hEq2] at hhs
        rw [hEq]
        exact hhs
      · rw [image_eq_zero_of_notMem_tsupport hw]
        simp only [zero_smul]
        exact hasSum_zero
    have hmeas : ∀ k : ℕ, AEStronglyMeasurable
        (fun w : ℂ => K w • (coef k w (fun _ => y)))
        (volume.restrict (tsupport K)) := by
      intro k
      have h2 : AEStronglyMeasurable (fun w : ℂ => coef k w (fun _ => y))
          (volume.restrict (tsupport K)) :=
        (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => X) ℂ
          (fun _ => y)).continuous).comp_continuousOn (hcoef_cont k))
          |>.aestronglyMeasurable (isClosed_tsupport K).measurableSet
      exact hKm.restrict.smul h2
    have hdom : ∀ k : ℕ, ∀ᵐ w ∂(volume.restrict (tsupport K)),
        ‖K w • (coef k w (fun _ => y))‖ ≤ ‖K w‖ * (C * (‖y‖ / R) ^ k) := by
      intro k
      refine Filter.Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ tsupport K
      · have hb := hcoef_bound k w hw
        rw [norm_smul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖coef k w (fun _ => y)‖ ≤ ‖coef k w‖ * ‖y‖ ^ k := by
              refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ C * (‖y‖ / R) ^ k := by
              calc ‖coef k w‖ * ‖y‖ ^ k ≤ (C / R ^ k) * ‖y‖ ^ k := by
                    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) k)
                    rw [le_div_iff₀ (pow_pos hRpos k)]
                    linarith [hb]
                _ = C * (‖y‖ / R) ^ k := by rw [div_pow]; ring
      · rw [image_eq_zero_of_notMem_tsupport hw]
        simp
    have hsumm : ∀ᵐ w ∂(volume.restrict (tsupport K)),
        Summable fun k : ℕ => ‖K w‖ * (C * (‖y‖ / R) ^ k) := by
      refine Filter.Eventually.of_forall fun w => ?_
      have h := (summable_geometric_of_lt_one hq0 hq1).mul_left (‖K w‖ * C)
      simpa only [mul_assoc] using h
    have hIntBound : Integrable (fun w : ℂ => ∑' k : ℕ, ‖K w‖ * (C * (‖y‖ / R) ^ k))
        (volume.restrict (tsupport K)) := by
      have hEq : (fun w : ℂ => ∑' k : ℕ, ‖K w‖ * (C * (‖y‖ / R) ^ k))
          = fun w : ℂ => ‖K w‖ * (C * (1 - ‖y‖ / R)⁻¹) := by
        funext w
        have h1 : (∑' k : ℕ, C * (‖y‖ / R) ^ k) = C * (1 - ‖y‖ / R)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        rw [tsum_mul_left, h1]
      rw [hEq]
      exact hIθ.mul_const _
    have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (tsupport K))
      (F := fun (k : ℕ) (w : ℂ) => K w • (coef k w (fun _ => y)))
      (f := fun (w : ℂ) => K w • F (z₀ + y, w))
      (fun (k : ℕ) (w : ℂ) => ‖K w‖ * (C * (‖y‖ / R) ^ k)) hmeas hdom hsumm hIntBound hpt
    have hfun : (fun k : ℕ => ∫ w : ℂ,
          K w • (coef k w (fun _ => y)) ∂(volume.restrict (tsupport K)))
        = fun k : ℕ => a k (fun _ => y) := by
      funext k
      rw [hadef, ContinuousMultilinearMap.integral_apply (hInt k)]
      simp only [smul_apply]
    rw [hfun] at hmain
    have hEqInt : (∫ w in tsupport K, K w • F (z₀ + y, w)) = ∫ w, K w • F (z₀ + y, w) :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
        rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]
    rw [hEqInt] at hmain
    exact hmain
  -- ## Step 6: assemble
  refine ⟨a, R.toNNReal, hle_radius, ?_, ?_⟩
  · exact ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hRpos)
  · intro y hy
    rw [Metric.mem_eball] at hy
    have hyR : ‖y‖ < R := by
      have h1 : ‖y‖₊ < R.toNNReal := by
        rwa [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hy
      have h2 := (NNReal.coe_lt_coe (r₁ := ‖y‖₊) (r₂ := R.toNNReal)).mpr h1
      rwa [coe_nnnorm, Real.coe_toNNReal R hRpos.le] at h2
    simpa only [smul_eq_mul] using hHasSum y hyR

end Work.NN.Core.TelTwoDF
