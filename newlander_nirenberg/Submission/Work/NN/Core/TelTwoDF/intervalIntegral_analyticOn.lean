import Mathlib
import Submission.Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound

/-!
# Real analyticity of an interval integral with an analytic parameter dependence

If `F : X × ℝ → ℂ` is real analytic on the open set `Ω ×ˢ Ioo (a - ε) (b + ε)` (with `a ≤ b`,
`ε > 0`), then the parameter integral `x ↦ ∫ t in a..b, F (x, t)` is real analytic on `Ω`.

The proof expands, for every `t` in the compact interval `[a, b]`, the function `F (·, t)` in
its power series at the point `(z₀, t)` of the compact set `{z₀} × [a, b]`, the uniformity of
the expansion being supplied by `Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound`; the
interchange of the sum and the Bochner integral is
`MeasureTheory.hasSum_integral_of_dominated_convergence`.
-/

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Metric Set
open scoped Topology

theorem intervalIntegral_analyticOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) {F : X × ℝ → ℂ}
    (hF : AnalyticOn ℝ F (Ω ×ˢ Set.Ioo (a - ε) (b + ε))) :
    AnalyticOn ℝ (fun x : X => ∫ t in a..b, F (x, t)) Ω := by
  classical
  have hfun_eq : (fun x : X => ∫ t in a..b, F (x, t)) =
      (fun x : X => ∫ t in Set.Ioc a b, F (x, t)) :=
    funext fun x => intervalIntegral.integral_of_le (μ := volume) hab
  rw [hfun_eq]
  rw [hΩ.analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  set K : Set (X × ℝ) := {z₀} ×ˢ Set.Icc a b with hKdef
  have hKc : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hUopen : IsOpen (Ω ×ˢ Set.Ioo (a - ε) (b + ε)) := hΩ.prod isOpen_Ioo
  have hKsub : K ⊆ Ω ×ˢ Set.Ioo (a - ε) (b + ε) := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨hz₀, ?_⟩
    rw [Set.mem_Ioo]
    rw [Set.mem_Icc] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨R, hRpos, C, hCpos, hconv, hbound⟩ :=
    analytic_uniform_taylor_bound hUopen hF hKc hKsub
  set coef : (k : ℕ) → ℝ → (X [×k]→L[ℝ] ℂ) := fun k t =>
    (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)).compContinuousLinearMap
      (fun _ : Fin k => ContinuousLinearMap.inl ℝ X ℝ) with hcoefdef
  have hcoef_apply : ∀ (k : ℕ) (t : ℝ) (v : Fin k → X),
      coef k t v = ((k.factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ k F (z₀, t) (fun i => (v i, 0)) := by
    intro k t v
    rw [hcoefdef]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inl_apply, smul_apply]
  have hnorm_inl : ‖ContinuousLinearMap.inl ℝ X ℝ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [ContinuousLinearMap.inl_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x),
      one_mul]
  have hcoef_bound : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc a b → ‖coef k t‖ * R ^ k ≤ C := by
    intro k t ht
    have hp : (z₀, t) ∈ K := by
      rw [hKdef]; exact ⟨rfl, ht⟩
    have hb := hbound (z₀, t) hp k
    have hle : ‖coef k t‖ ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ := by
      have hprod : ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ X ℝ‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hnorm_inl
      rw [hcoefdef]
      refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
      calc ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ *
              ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ X ℝ‖
          ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ := mul_one _
    calc ‖coef k t‖ * R ^ k
        ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ * R ^ k :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hRpos.le k)
      _ ≤ C := hb
  have hiter_cont : ∀ k : ℕ, ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ k F (z₀, t))
      (Set.Icc a b) := by
    intro k t ht
    have htU : (z₀, t) ∈ Ω ×ˢ Set.Ioo (a - ε) (b + ε) := by
      refine ⟨hz₀, ?_⟩
      rw [Set.mem_Ioo]
      rw [Set.mem_Icc] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hAnal : AnalyticAt ℝ F (z₀, t) := hF.analyticAt (hUopen.mem_nhds htU)
    have hcA : ContinuousAt (iteratedFDeriv ℝ k F) (z₀, t) :=
      (hAnal.contDiffAt (n := ⊤)).continuousAt_iteratedFDeriv le_top
    exact hcA.comp_continuousWithinAt
      (continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩).continuousWithinAt
  have hcoef_cont : ∀ k : ℕ, ContinuousOn (fun t : ℝ => coef k t) (Set.Icc a b) := by
    intro k
    have h1 : ContinuousOn (fun t : ℝ => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t))
        (Set.Icc a b) := (hiter_cont k).const_smul ((k.factorial : ℝ)⁻¹)
    have h2 : ContinuousOn (fun t : ℝ =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ X ℝ))
          (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t))) (Set.Icc a b) :=
      (ContinuousLinearMap.continuous _).comp_continuousOn h1
    convert h2 using 1
    ext t
    rw [hcoefdef, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  have hInt : ∀ k : ℕ, IntegrableOn (fun t : ℝ => coef k t) (Set.Ioc a b) volume := by
    intro k
    exact ((hcoef_cont k).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  set p : FormalMultilinearSeries ℝ X ℂ := fun k => ∫ t in Set.Ioc a b, coef k t with hpdef
  have hp_bound : ∀ k : ℕ, ‖p k‖ * R ^ k ≤ C * (volume (Set.Ioc a b)).toReal := by
    intro k
    have hCk : ∀ t ∈ Set.Ioc a b, ‖coef k t‖ ≤ C / R ^ k := by
      intro t ht
      rw [le_div_iff₀ (pow_pos hRpos k)]
      exact hcoef_bound k t (Ioc_subset_Icc_self ht)
    have h1 : ‖p k‖ ≤ (C / R ^ k) * (volume (Set.Ioc a b)).toReal := by
      rw [hpdef]
      exact norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hCk
    calc ‖p k‖ * R ^ k
        ≤ ((C / R ^ k) * (volume (Set.Ioc a b)).toReal) * R ^ k :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hRpos.le k)
      _ = C * (volume (Set.Ioc a b)).toReal := by
          rw [mul_assoc, mul_comm (volume (Set.Ioc a b)).toReal (R ^ k), ← mul_assoc,
            div_mul_cancel₀ C (pow_ne_zero k (ne_of_gt hRpos))]
  have hle_radius : ((R.toNNReal : NNReal) : ENNReal) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound p (C * (volume (Set.Ioc a b)).toReal) fun k => ?_
    rw [Real.coe_toNNReal R hRpos.le]
    exact hp_bound k
  have hHasSum : ∀ y : X, ‖y‖ < R →
      HasSum (fun k : ℕ => p k (fun _ => y)) (∫ t in Set.Ioc a b, F (z₀ + y, t)) := by
    intro y hy
    have hq0 : 0 ≤ ‖y‖ / R := div_nonneg (norm_nonneg _) hRpos.le
    have hq1 : ‖y‖ / R < 1 := (div_lt_one hRpos).mpr hy
    have hF_meas : ∀ k : ℕ, AEStronglyMeasurable
        (fun t : ℝ => coef k t (fun _ => y)) (volume.restrict (Set.Ioc a b)) := by
      intro k
      have hcont : ContinuousOn (fun t : ℝ => coef k t (fun _ => y)) (Set.Ioc a b) :=
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => X) ℂ (fun _ => y)).continuous).comp_continuousOn
          ((hcoef_cont k).mono Ioc_subset_Icc_self)
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    have h_bound : ∀ k : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖coef k t (fun _ => y)‖ ≤ C * (‖y‖ / R) ^ k := by
      intro k
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have hb := hcoef_bound k t (Ioc_subset_Icc_self ht)
      calc ‖coef k t (fun _ => y)‖ ≤ ‖coef k t‖ * ‖y‖ ^ k := by
            refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ C * (‖y‖ / R) ^ k := by
            calc ‖coef k t‖ * ‖y‖ ^ k ≤ (C / R ^ k) * ‖y‖ ^ k := by
                  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) k)
                  rw [le_div_iff₀ (pow_pos hRpos k)]
                  linarith [hb]
              _ = C * (‖y‖ / R) ^ k := by rw [div_pow]; ring
    have hbound_summable : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        Summable (fun k : ℕ => C * (‖y‖ / R) ^ k) :=
      Filter.Eventually.of_forall fun t => (summable_geometric_of_lt_one hq0 hq1).mul_left C
    have hbound_integrable : Integrable
        (fun t : ℝ => ∑' k : ℕ, C * (‖y‖ / R) ^ k) (volume.restrict (Set.Ioc a b)) := by
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
      have hconst : (fun t : ℝ => ∑' k : ℕ, C * (‖y‖ / R) ^ k) =
          fun _ => C * (1 - ‖y‖ / R)⁻¹ := by
        funext t
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rw [hconst]
      exact integrable_const _
    have h_lim : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        HasSum (fun k : ℕ => coef k t (fun _ => y)) (F (z₀ + y, t)) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have htIcc : t ∈ Set.Icc a b := Ioc_subset_Icc_self ht
      have hp : (z₀, t) ∈ K := by
        rw [hKdef]; exact ⟨rfl, htIcc⟩
      have hy' : ‖(y, (0 : ℝ))‖ < R := by
        rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg y)]; exact hy
      have hhs := hconv (z₀, t) hp (y, 0) hy'
      have hEq : (fun k : ℕ => coef k t (fun _ => y)) =
          fun k : ℕ => ((k.factorial : ℝ)⁻¹) •
            iteratedFDeriv ℝ k F (z₀, t) (fun _ => (y, (0 : ℝ))) := by
        funext k
        rw [hcoef_apply k t (fun _ => y)]
      have hEq2 : (z₀, t) + (y, (0 : ℝ)) = (z₀ + y, t) := by simp [Prod.mk_add_mk]
      rw [hEq2] at hhs
      rw [hEq]
      exact hhs
    have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioc a b))
      (F := fun (k : ℕ) (t : ℝ) => coef k t (fun _ => y))
      (f := fun t : ℝ => F (z₀ + y, t))
      (bound := fun (k : ℕ) (t : ℝ) => C * (‖y‖ / R) ^ k)
      hF_meas h_bound hbound_summable hbound_integrable h_lim
    have hfun : (fun k : ℕ => ∫ t, coef k t (fun _ => y) ∂(volume.restrict (Set.Ioc a b))) =
        fun k : ℕ => p k (fun _ => y) := by
      funext k
      rw [hpdef]
      exact (ContinuousMultilinearMap.integral_apply (hInt k) (fun _ => y)).symm
    rw [hfun] at hmain
    exact hmain
  refine ⟨p, R.toNNReal, hle_radius, ?_, ?_⟩
  · exact ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hRpos)
  · intro y hy
    rw [Metric.mem_eball] at hy
    have hyR : ‖y‖ < R := by
      have h1 : ‖y‖₊ < R.toNNReal := by
        rwa [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hy
      have h2 := (NNReal.coe_lt_coe (r₁ := ‖y‖₊) (r₂ := R.toNNReal)).mpr h1
      rwa [coe_nnnorm, Real.coe_toNNReal R hRpos.le] at h2
    exact hHasSum y hyR

end Work.NN.Core.TelTwoDF
