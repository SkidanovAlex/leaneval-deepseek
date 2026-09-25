import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport
import Submission.Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound

/-!
# Real analyticity of a parameter integral against a finite measure

We prove that for a finite measure `μ` on `Fin m → ℝ` which is concentrated on a compact set
`K` (i.e. `μ Kᶜ = 0`, `μ K < ⊤`), an open set `U ⊇ K`, and a function `F` which is real analytic
on `Ω × U`, the function

`z ↦ ∫ t, F (z, t) ∂μ`

is real analytic on `Ω`.

This generalises `Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport` from a smooth
compactly supported Lebesgue density to an arbitrary finite measure concentrated on a compact
set.  The proof is the same: at a point `z₀ ∈ Ω` one expands `F (z₀ + y, t)` in the power series
of `F` at `(z₀, t)` for every `t ∈ K`, the uniformity in `t` of the Taylor coefficients on the
compact set `{z₀} × K` being supplied by `Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound`;
the interchange of the sum and the integral is
`MeasureTheory.hasSum_integral_of_dominated_convergence`, the dominating functions being the
constants `C * (‖y‖ / R) ^ k` (no weight is needed any more: the finiteness of `μ K` replaces the
integrability of the weight).

Since `μ Kᶜ = 0` implies `μ.restrict K = μ` (`Measure.restrict_eq_self_of_ae_mem`), everything is
carried out for the restricted measure `μ.restrict K`, which is finite.
-/

set_option linter.style.haveILetI false

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Metric Set
open scoped Topology

/-- The inclusion of a factor into a product has operator norm at most one. -/
private lemma norm_inl_le_one_prod (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ‖ContinuousLinearMap.inl ℝ E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [ContinuousLinearMap.inl_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x),
    one_mul]

/-- **Real analyticity of a parameter integral against a finite measure.**

If `F` is real analytic on `Ω ×ˢ U`, where `U` is an open set containing the compact set `K`,
and `μ` is a measure supported in `K` with `μ K < ⊤`, then `z ↦ ∫ t, F (z, t) ∂μ` is real
analytic on `Ω`.  This generalises `Work.NN.Core.TelTwoDF.analyticOn_integral_disc_tsupport`
(the case where `μ` is a smooth compactly supported weight times Lebesgue measure) from a
Lebesgue density to an arbitrary finite measure on `K`; the proof is the same: for `t` fixed,
expand `F (z₀ + y, t)` in the power series of `F` at `(z₀, t)`, use
`Work.NN.Core.TelTwoDF.analytic_uniform_taylor_bound` for uniform bounds on the compact set
`{z₀} × K`, and `MeasureTheory.hasSum_integral_of_dominated_convergence` for the interchange of
sum and integral.  The finiteness hypothesis `μ K < ⊤` (rather than `[IsFiniteMeasure μ]`) only
records the fact that is actually used. -/
theorem analyticOn_integral_compact {n m : ℕ} {μ : MeasureTheory.Measure (Fin m → ℝ)}
    {K : Set (Fin m → ℝ)} (hK : IsCompact K) (hμK : μ Kᶜ = 0) (hμfin : μ K < ⊤)
    {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin n → ℂ) × (Fin m → ℝ) → ℂ} (hF : AnalyticOn ℝ F (Ω ×ˢ U)) :
    AnalyticOn ℝ (fun z : Fin n → ℂ => MeasureTheory.integral μ (fun t => F (z, t))) Ω := by
  classical
  -- `μ` is concentrated on `K`, so the restricted measure is `μ` itself.
  have hKae : ∀ᵐ t ∂μ, t ∈ K := by
    rw [MeasureTheory.ae_iff]
    simpa [Set.compl_def] using hμK
  have hμeq : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hKae
  suffices h : AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ t, F (z, t) ∂(μ.restrict K)) Ω by
    rwa [hμeq] at h
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμfin⟩
  rw [hΩ.analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  -- ## Step 1: a neighbourhood of `z₀` and the compact parameter set `closedBall z₀ ρ × K`
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz₀)
  set ρ : ℝ := ε / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρball : Metric.closedBall z₀ ρ ⊆ Ω :=
    (Metric.closedBall_subset_ball (by rw [hρdef]; linarith)).trans hε
  set Kc : Set ((Fin n → ℂ) × (Fin m → ℝ)) := Metric.closedBall z₀ ρ ×ˢ K with hKcdef
  have hKcc : IsCompact Kc := (isCompact_closedBall z₀ ρ).prod hK
  have hUopen : IsOpen (Ω ×ˢ U) := hΩ.prod hU
  have hKcsub : Kc ⊆ Ω ×ˢ U := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    exact ⟨hρball hz, hKU ht⟩
  obtain ⟨R, hRpos, C, hCpos, hconv, hbound⟩ :=
    analytic_uniform_taylor_bound hUopen hF hKcc hKcsub
  -- ## Step 2: the coefficient maps of the candidate power series
  set coef : (k : ℕ) → (Fin m → ℝ) → ((Fin n → ℂ) [×k]→L[ℝ] ℂ) := fun k t =>
    (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)).compContinuousLinearMap
      (fun _ : Fin k => ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin m → ℝ)) with hcoefdef
  have hcoef_apply : ∀ (k : ℕ) (t : Fin m → ℝ) (v : Fin k → (Fin n → ℂ)),
      coef k t v = ((k.factorial : ℝ)⁻¹) •
        iteratedFDeriv ℝ k F (z₀, t) (fun i => (v i, 0)) := by
    intro k t v
    rw [hcoefdef]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inl_apply, smul_apply]
  have hcoef_bound : ∀ (k : ℕ) (t : Fin m → ℝ), t ∈ K → ‖coef k t‖ * R ^ k ≤ C := by
    intro k t ht
    have hp : (z₀, t) ∈ Kc := by
      rw [hKcdef]; exact ⟨Metric.mem_closedBall_self hρpos.le, ht⟩
    have hb := hbound (z₀, t) hp k
    have hle : ‖coef k t‖ ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ := by
      have hprod : ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin m → ℝ)‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) (norm_inl_le_one_prod _ _)
      rw [hcoefdef]
      refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
      calc ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ *
              ∏ _ : Fin k, ‖ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin m → ℝ)‖
          ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ := mul_one _
    calc ‖coef k t‖ * R ^ k
        ≤ ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)‖ * R ^ k :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hRpos.le k)
      _ ≤ C := hb
  -- ## Step 3: continuity of the coefficient maps in the parameter
  have hiter_cont : ∀ k : ℕ,
      ContinuousOn (fun t : Fin m → ℝ => iteratedFDeriv ℝ k F (z₀, t)) K := by
    intro k t ht
    have htU : (z₀, t) ∈ Ω ×ˢ U := ⟨hz₀, hKU ht⟩
    have hAnal : AnalyticAt ℝ F (z₀, t) := hF.analyticAt (hUopen.mem_nhds htU)
    have hcA : ContinuousAt (iteratedFDeriv ℝ k F) (z₀, t) :=
      (hAnal.contDiffAt (n := ⊤)).continuousAt_iteratedFDeriv le_top
    exact hcA.comp_continuousWithinAt
      (continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩).continuousWithinAt
  have hcoef_cont : ∀ k : ℕ, ContinuousOn (fun t : Fin m → ℝ => coef k t) K := by
    intro k
    have h1 : ContinuousOn
        (fun t : Fin m → ℝ => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t)) K :=
      (hiter_cont k).const_smul ((k.factorial : ℝ)⁻¹)
    have h2 : ContinuousOn (fun t : Fin m → ℝ =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin m → ℝ)))
          (((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F (z₀, t))) K :=
      (ContinuousLinearMap.continuous _).comp_continuousOn h1
    convert h2 using 1
    ext t
    rw [hcoefdef, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  -- ## Step 4: the candidate power series
  have hcoef_int : ∀ k : ℕ, Integrable (fun t : Fin m → ℝ => coef k t) (μ.restrict K) := by
    intro k
    refine Integrable.of_bound ?_ (C / R ^ k) ?_
    · exact (hcoef_cont k).aestronglyMeasurable hK.isClosed.measurableSet
    · rw [MeasureTheory.ae_restrict_iff' hK.isClosed.measurableSet]
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [le_div_iff₀ (pow_pos hRpos k)]
      exact hcoef_bound k t ht
  set a : FormalMultilinearSeries ℝ (Fin n → ℂ) ℂ :=
    fun k => ∫ t, coef k t ∂(μ.restrict K) with hadef
  have ha_bound : ∀ k : ℕ, ‖a k‖ * R ^ k ≤ (μ K).toReal * C := by
    intro k
    have h1 : ‖a k‖ ≤ C / R ^ k * (μ K).toReal := by
      rw [hadef]
      have h2 := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
        (f := fun t : Fin m → ℝ => coef k t) (C := C / R ^ k) ?_
      · rw [MeasureTheory.measureReal_restrict_apply_univ] at h2
        exact h2
      · rw [MeasureTheory.ae_restrict_iff' hK.isClosed.measurableSet]
        refine Filter.Eventually.of_forall fun t ht => ?_
        rw [le_div_iff₀ (pow_pos hRpos k)]
        exact hcoef_bound k t ht
    calc ‖a k‖ * R ^ k ≤ (C / R ^ k * (μ K).toReal) * R ^ k :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hRpos.le k)
      _ = (μ K).toReal * C := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt (pow_pos hRpos k))]
          ring
  have hle_radius : ((R.toNNReal : NNReal) : ENNReal) ≤ a.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound a ((μ K).toReal * C) fun k => ?_
    rw [Real.coe_toNNReal R hRpos.le]
    exact ha_bound k
  -- ## Step 5: the power series sums to the integral
  have hHasSum : ∀ y : Fin n → ℂ, ‖y‖ < R →
      HasSum (fun k : ℕ => a k (fun _ => y)) (∫ t, F (z₀ + y, t) ∂(μ.restrict K)) := by
    intro y hy
    have hq0 : 0 ≤ ‖y‖ / R := div_nonneg (norm_nonneg _) hRpos.le
    have hq1 : ‖y‖ / R < 1 := (div_lt_one hRpos).mpr hy
    have hpt : ∀ᵐ t ∂(μ.restrict K),
        HasSum (fun k : ℕ => coef k t (fun _ => y)) (F (z₀ + y, t)) := by
      rw [MeasureTheory.ae_restrict_iff' hK.isClosed.measurableSet]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have hp : (z₀, t) ∈ Kc := by
        rw [hKcdef]; exact ⟨Metric.mem_closedBall_self hρpos.le, ht⟩
      have hy' : ‖(y, (0 : Fin m → ℝ))‖ < R := by
        rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg y)]; exact hy
      have hhs := hconv (z₀, t) hp (y, 0) hy'
      have hEq : (fun i : ℕ => coef i t (fun _ => y))
          = fun i : ℕ => ((i.factorial : ℝ)⁻¹) •
              iteratedFDeriv ℝ i F (z₀, t) (fun _ => (y, 0)) := by
        funext i
        rw [hcoef_apply i t (fun _ => y)]
      have hEq2 : (z₀, t) + (y, (0 : Fin m → ℝ)) = (z₀ + y, t) := by
        simp [Prod.mk_add_mk]
      rw [hEq2] at hhs
      rw [hEq]
      exact hhs
    have hmeas : ∀ k : ℕ, AEStronglyMeasurable
        (fun t : Fin m → ℝ => coef k t (fun _ => y)) (μ.restrict K) := by
      intro k
      have h2 : ContinuousOn (fun t : Fin m → ℝ => coef k t (fun _ => y)) K :=
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ
          (fun _ => y)).continuous).comp_continuousOn (hcoef_cont k)
      exact h2.aestronglyMeasurable hK.isClosed.measurableSet
    have hdom : ∀ k : ℕ, ∀ᵐ t ∂(μ.restrict K),
        ‖coef k t (fun _ => y)‖ ≤ C * (‖y‖ / R) ^ k := by
      intro k
      rw [MeasureTheory.ae_restrict_iff' hK.isClosed.measurableSet]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have hb := hcoef_bound k t ht
      calc ‖coef k t (fun _ => y)‖ ≤ ‖coef k t‖ * ‖y‖ ^ k := by
            refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ C * (‖y‖ / R) ^ k := by
            calc ‖coef k t‖ * ‖y‖ ^ k ≤ (C / R ^ k) * ‖y‖ ^ k := by
                  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) k)
                  rw [le_div_iff₀ (pow_pos hRpos k)]
                  linarith [hb]
              _ = C * (‖y‖ / R) ^ k := by rw [div_pow]; ring
    have hsumm : ∀ᵐ t ∂(μ.restrict K), Summable fun k : ℕ => C * (‖y‖ / R) ^ k :=
      Filter.Eventually.of_forall fun t => (summable_geometric_of_lt_one hq0 hq1).mul_left C
    have hIntBound : Integrable (fun t : Fin m → ℝ => ∑' k : ℕ, C * (‖y‖ / R) ^ k)
        (μ.restrict K) := by
      have h : (fun t : Fin m → ℝ => ∑' k : ℕ, C * (‖y‖ / R) ^ k)
          = fun _ => C * (1 - ‖y‖ / R)⁻¹ := by
        funext t
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rw [h]
      exact integrable_const _
    have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := μ.restrict K)
      (F := fun (k : ℕ) (t : Fin m → ℝ) => coef k t (fun _ => y))
      (f := fun (t : Fin m → ℝ) => F (z₀ + y, t))
      (fun (k : ℕ) (t : Fin m → ℝ) => C * (‖y‖ / R) ^ k) hmeas hdom hsumm hIntBound hpt
    have hfun : (fun k : ℕ => ∫ t : Fin m → ℝ, coef k t (fun _ => y) ∂(μ.restrict K))
        = fun k : ℕ => a k (fun _ => y) := by
      funext k
      rw [hadef, ContinuousMultilinearMap.integral_apply (hcoef_int k)]
    rw [hfun] at hmain
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
    exact hHasSum y hyR

end Work.NN.Core.TelTwoDF
