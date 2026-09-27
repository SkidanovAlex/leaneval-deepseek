import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.surjDefs
import Submission.Work.Mostow.visualConcentration
import Submission.Work.Mostow.smoothRetraction
import Submission.Work.Mostow.noRetractionSmooth

/-!
# `Work.Mostow.natMapSurj`

The natural map `natMap φ` of a boundary homeomorphism `φ` of `Sph n` is onto.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## Measurability and pushforward of the visual measure -/

section Pushforward

variable {φ : E n → E n}

/-- A map continuous on the boundary sphere is a.e. measurable for any measure living on it. -/
lemma aemeasurable_of_continuousOn_sphere (hcont : ContinuousOn φ (Sph n)) (μ : Measure (E n))
    (hμ : μ (Sph n)ᶜ = 0) : AEMeasurable φ μ := by
  have hSp : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet
  have hcont' : Continuous ((Sph n).domRestrict φ) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  have hmeas : Measurable (fun x : (Sph n : Set (E n)) => φ x) := hcont'.measurable
  have hae : AEMeasurable φ (μ.restrict (Sph n)) :=
    aemeasurable_restrict_of_measurable_subtype hSp hmeas
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)] at hae

lemma map_visual_apply (hV : VisualProp n) (hcont : ContinuousOn φ (Sph n)) (u : E n)
    (s : Set (E n)) (hs : MeasurableSet s) :
    ((visual n u).map φ) s = visual n u (φ ⁻¹' s) :=
  Measure.map_apply_of_aemeasurable
    (aemeasurable_of_continuousOn_sphere hcont _ (hV u).2.1) hs

lemma map_visual_isProbability (hV : VisualProp n) (hcont : ContinuousOn φ (Sph n)) (u : E n) :
    IsProbabilityMeasure ((visual n u).map φ) :=
  (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_of_continuousOn_sphere hcont _ (hV u).2.1)).mpr (hV u).1

lemma map_visual_compl_sphere (hV : VisualProp n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hcont : ContinuousOn φ (Sph n)) (u : E n) :
    ((visual n u).map φ) (Sph n)ᶜ = 0 := by
  rw [map_visual_apply hV hcont u (Sph n)ᶜ (Metric.isClosed_sphere.measurableSet.compl)]
  refine measure_mono_null ?_ (hV u).2.1
  intro x hx
  exact fun hxS => hx (hbij.mapsTo hxS)

lemma map_visual_singleton (hV : VisualProp n) (hbij : Set.BijOn φ (Sph n) (Sph n))
    (hcont : ContinuousOn φ (Sph n)) (u : E n) (ξ : E n) :
    ((visual n u).map φ) {ξ} = 0 := by
  rw [map_visual_apply hV hcont u {ξ} (measurableSet_singleton ξ)]
  by_cases hξ : ξ ∈ Sph n
  · obtain ⟨w, hwS, hw⟩ := hbij.surjOn hξ
    have hsub : φ ⁻¹' {ξ} ⊆ (Sph n)ᶜ ∪ {w} := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      by_cases hxS : x ∈ Sph n
      · refine Or.inr (Set.mem_singleton_iff.mpr ?_)
        exact hbij.injOn hxS hwS (by rw [hx, hw])
      · exact Or.inl hxS
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨(hV u).2.1, (hV u).2.2.1 w⟩
  · have hsub : φ ⁻¹' {ξ} ⊆ (Sph n)ᶜ := by
      intro x hx hxS
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      exact hξ (hx ▸ hbij.mapsTo hxS)
    exact measure_mono_null hsub (hV u).2.1

/-- If `φ` maps the `ε'`-ball around `ξ` into the `ε`-ball around `η`, then the pushforward of the
visual measure gives the complementary ball at most the visual mass of the complementary ball. -/
lemma map_visual_compl_ball (hV : VisualProp n) (hcont : ContinuousOn φ (Sph n)) (u : E n)
    {ξ η : E n} {ε ε' : ℝ}
    (hball : ∀ θ ∈ Sph n, ‖θ - ξ‖ < ε' → ‖φ θ - η‖ < ε) :
    ((visual n u).map φ) ((ball η ε)ᶜ) ≤ visual n u ((ball ξ ε')ᶜ) := by
  rw [map_visual_apply hV hcont u (Metric.ball η ε)ᶜ (Metric.isOpen_ball.measurableSet.compl)]
  calc visual n u (φ ⁻¹' (ball η ε)ᶜ)
      ≤ visual n u ((ball ξ ε')ᶜ ∪ (Sph n)ᶜ) := measure_mono ?_
    _ ≤ visual n u ((ball ξ ε')ᶜ) + visual n u (Sph n)ᶜ := measure_union_le _ _
    _ = visual n u ((ball ξ ε')ᶜ) := by rw [(hV u).2.1, add_zero]
  intro x hx
  by_cases hxS : x ∈ Sph n
  · refine Or.inl ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, mem_ball, dist_eq_norm] at hx ⊢
    exact fun hlt => hx (hball x hxS hlt)
  · exact Or.inr hxS

end Pushforward


/-! ## Boundary continuity of the natural map -/

/-! ## The barycentre of a concentrated measure (own proof, for the boundary estimate) -/

private lemma barConc_self (n : ℕ) (hB : BaryProp n) (ν : Measure (E n))
    (hν : IsProbabilityMeasure ν) (hsupp : ν (Sph n)ᶜ = 0) (hnt : ∀ ξ, ν {ξ} = 0)
    (η : E n) (hη : η ∈ Sph n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcap : ν ((Metric.ball η ε)ᶜ) ≤ ENNReal.ofReal (1 / 4)) :
    ‖kappa (bar ν) - η‖ ≤ ε + 8 * ε ^ (1 / 3 : ℝ) := by
  classical
  have hνuniv : ν Set.univ = 1 := measure_univ
  set b : E n := kappa (bar ν) with hbdef
  have hb1 : ‖b‖ < 1 := by rw [hbdef]; exact norm_kappa_lt_one (bar ν)
  have hb0 : (0:ℝ) < 1 - ‖b‖ := by linarith [norm_nonneg b]
  set ρ : ℝ := ‖b - η‖ with hρdef
  have hρ2 : ρ < 2 := by
    have h1 : ‖b - η‖ ≤ ‖b‖ + ‖η‖ := norm_sub_le _ _
    rw [norm_eq_one_of_mem_Sph hη] at h1
    rw [hρdef]; linarith [norm_nonneg b]
  by_cases hle : ρ ≤ ε
  · have h4 : 0 ≤ 8 * ε ^ (1 / 3 : ℝ) := by positivity
    linarith
  · have hgt : ε < ρ := lt_of_not_ge hle
    have hρε : 0 < ρ - ε := by linarith
    set bt : E n := (1 - ε) • η with hbtdef
    have hbt_norm : ‖bt‖ = 1 - ε := by
      rw [hbtdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ε),
        norm_eq_one_of_mem_Sph hη, mul_one]
    have hbt1 : ‖bt‖ < 1 := by rw [hbt_norm]; linarith
    have hbt_eta : ‖bt - η‖ = ε := by
      have h1 : bt - η = (-ε) • η := by
        rw [hbtdef]
        module
      rw [h1, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hε0, norm_eq_one_of_mem_Sph hη,
        mul_one]
    set Cap : Set (E n) := Metric.ball η ε with hCapdef
    have hCapm : MeasurableSet Cap := Metric.isOpen_ball.measurableSet
    have hCapCm : MeasurableSet Capᶜ := hCapm.compl
    have hae_sph : ∀ᵐ x ∂ν, x ∈ Sph n := ae_iff.mpr hsupp
    -- measure bookkeeping
    have hCapC_le_one : ν Capᶜ ≤ 1 := by
      calc ν Capᶜ ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hCapC_ne : ν Capᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hCapC_le_one
    set δ : ℝ := ν.real Capᶜ with hδdef
    have hδ0 : 0 ≤ δ := by rw [hδdef, Measure.real]; exact ENNReal.toReal_nonneg
    have hδle : δ ≤ 1 / 4 := by
      rw [hδdef, Measure.real]
      calc (ν Capᶜ).toReal ≤ (ENNReal.ofReal (1 / 4)).toReal :=
            ENNReal.toReal_mono (by simp) hcap
        _ = 1 / 4 := ENNReal.toReal_ofReal (by norm_num)
    have hCapreal : ν.real Cap = 1 - δ := by
      have h1 : ν Cap = ν Set.univ - ν Capᶜ := by
        rw [← compl_compl Cap, measure_compl hCapCm hCapC_ne, compl_compl]
      rw [hδdef, Measure.real, h1, hνuniv,
        ENNReal.toReal_sub_of_le hCapC_le_one ENNReal.one_ne_top]
      rfl
    -- integrability
    have hIntb : Integrable (fun ξ => Real.log ‖b - ξ‖) ν := integrable_log_dist ν hsupp hb1
    have hIntt : Integrable (fun ξ => Real.log ‖bt - ξ‖) ν := integrable_log_dist ν hsupp hbt1
    -- membership facts for the cap
    have hcap_norm : ∀ x ∈ Cap, ‖x - η‖ < ε := by
      intro x hx
      rw [hCapdef, Metric.mem_ball, dist_eq_norm] at hx; exact hx
    -- lower bound for the `b` integral
    have hlow_cap : ν.real Cap * Real.log (ρ - ε) ≤ ∫ ξ in Cap, Real.log ‖b - ξ‖ ∂ν := by
      have hconst : ∫ ξ in Cap, (Real.log (ρ - ε) : ℝ) ∂ν = ν.real Cap * Real.log (ρ - ε) := by
        rw [setIntegral_const, smul_eq_mul]
      rw [← hconst]
      refine integral_mono_ae (integrable_const _) hIntb.restrict ?_
      filter_upwards [ae_restrict_mem hCapm] with x hx
      refine Real.log_le_log hρε ?_
      have h3 : ‖b - η‖ ≤ ‖b - x‖ + ‖x - η‖ := by
        have h4 := norm_add_le (b - x) (x - η)
        rwa [sub_add_sub_cancel] at h4
      rw [← hρdef] at h3
      linarith [hcap_norm x hx]
    have hlow_comp : ν.real Capᶜ * Real.log (1 - ‖b‖) ≤ ∫ ξ in Capᶜ, Real.log ‖b - ξ‖ ∂ν := by
      have hconst : ∫ ξ in Capᶜ, (Real.log (1 - ‖b‖) : ℝ) ∂ν
          = ν.real Capᶜ * Real.log (1 - ‖b‖) := by
        rw [setIntegral_const, smul_eq_mul]
      rw [← hconst]
      refine integral_mono_ae (integrable_const _) hIntb.restrict ?_
      filter_upwards [ae_restrict_mem hCapCm, ae_restrict_of_ae hae_sph] with x hx hxS
      refine Real.log_le_log hb0 ?_
      have hx1 : ‖x‖ = 1 := norm_eq_one_of_mem_Sph hxS
      have h4 := norm_sub_norm_le x b
      rw [hx1, norm_sub_rev] at h4
      linarith
    have hAb : (1 - δ) * Real.log (ρ - ε) + δ * Real.log (1 - ‖b‖)
        ≤ ∫ ξ, Real.log ‖b - ξ‖ ∂ν := by
      rw [hCapreal] at hlow_cap
      have hsplit := integral_add_compl hCapm hIntb
      linarith [hsplit, hlow_cap, hlow_comp]
    -- upper bound for the `bt` integral
    have hup_cap : ∫ ξ in Cap, Real.log ‖bt - ξ‖ ∂ν ≤ ν.real Cap * Real.log (2 * ε) := by
      have hconst : ∫ ξ in Cap, (Real.log (2 * ε) : ℝ) ∂ν = ν.real Cap * Real.log (2 * ε) := by
        rw [setIntegral_const, smul_eq_mul]
      rw [← hconst]
      refine integral_mono_ae hIntt.restrict (integrable_const _) ?_
      filter_upwards [ae_restrict_mem hCapm, ae_restrict_of_ae hae_sph] with x hx hxS
      have hx1 : ‖x‖ = 1 := norm_eq_one_of_mem_Sph hxS
      have hne : bt ≠ x := by
        intro h; rw [h] at hbt_norm; rw [hx1] at hbt_norm
        linarith
      refine Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) ?_
      have h3 : ‖bt - x‖ ≤ ‖bt - η‖ + ‖η - x‖ := by
        have h4 := norm_add_le (bt - η) (η - x)
        rwa [sub_add_sub_cancel] at h4
      rw [hbt_eta] at h3
      have h5 : ‖η - x‖ = ‖x - η‖ := norm_sub_rev _ _
      rw [h5] at h3
      linarith [hcap_norm x hx]
    have hup_comp : ∫ ξ in Capᶜ, Real.log ‖bt - ξ‖ ∂ν ≤ ν.real Capᶜ * Real.log 2 := by
      have hconst : ∫ ξ in Capᶜ, (Real.log 2 : ℝ) ∂ν = ν.real Capᶜ * Real.log 2 := by
        rw [setIntegral_const, smul_eq_mul]
      rw [← hconst]
      refine integral_mono_ae hIntt.restrict (integrable_const _) ?_
      filter_upwards [ae_restrict_mem hCapCm, ae_restrict_of_ae hae_sph] with x hx hxS
      have hx1 : ‖x‖ = 1 := norm_eq_one_of_mem_Sph hxS
      have hne : bt ≠ x := by
        intro h; rw [h] at hbt_norm; rw [hx1] at hbt_norm
        linarith
      refine Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) ?_
      have h4 : ‖bt - x‖ ≤ ‖bt‖ + ‖x‖ := norm_sub_le _ _
      rw [hbt_norm, hx1] at h4
      linarith
    have hAt : ∫ ξ, Real.log ‖bt - ξ‖ ∂ν ≤ (1 - δ) * Real.log (2 * ε) + δ * Real.log 2 := by
      rw [hCapreal] at hup_cap
      have hsplit := integral_add_compl hCapm hIntt
      linarith [hsplit, hup_cap, hup_comp]
    -- log bounds for the two normalisation terms
    have hC : Real.log (1 - ‖b‖ ^ 2) ≤ Real.log (1 - ‖b‖) + Real.log 2 := by
      have h1 : 1 - ‖b‖ ^ 2 = (1 - ‖b‖) * (1 + ‖b‖) := by ring
      rw [h1, Real.log_mul (ne_of_gt hb0) (by positivity)]
      have h2 : Real.log (1 + ‖b‖) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by linarith [norm_nonneg b, hb1.le])
      linarith
    have hCt : Real.log ε ≤ Real.log (1 - ‖bt‖ ^ 2) := by
      have h2 : ε ≤ 1 - ‖bt‖ ^ 2 := by
        rw [hbt_norm]; nlinarith [hε0, hε1]
      exact Real.log_le_log hε0 h2
    -- the comparison at the competitor
    have hmin := (hB ν hν hsupp hnt).1 (kappaInv bt)
    have hbb : baryFun ν (bar ν) = 2 * ∫ ξ, Real.log ‖b - ξ‖ ∂ν - Real.log (1 - ‖b‖ ^ 2) := by
      have h1 := baryFun_chart ν hνuniv hsupp (bar ν)
      rwa [← hbdef] at h1
    have hbtb : baryFun ν (kappaInv bt)
        = 2 * ∫ ξ, Real.log ‖bt - ξ‖ ∂ν - Real.log (1 - ‖bt‖ ^ 2) := by
      have h1 := baryFun_chart ν hνuniv hsupp (kappaInv bt)
      rwa [kappa_kappaInv bt hbt1] at h1
    have hkey : 2 * (1 - δ) * Real.log (ρ - ε) ≤ 2 * (1 - δ) * Real.log (2 * ε)
        + 2 * δ * Real.log 2 - Real.log ε + Real.log 2 := by
      have h3 : 2 * ((1 - δ) * Real.log (ρ - ε) + δ * Real.log (1 - ‖b‖))
          - Real.log (1 - ‖b‖ ^ 2)
          ≤ 2 * ((1 - δ) * Real.log (2 * ε) + δ * Real.log 2)
            - Real.log (1 - ‖bt‖ ^ 2) := by
        have hmin' : 2 * ∫ ξ, Real.log ‖b - ξ‖ ∂ν - Real.log (1 - ‖b‖ ^ 2)
            ≤ 2 * ∫ ξ, Real.log ‖bt - ξ‖ ∂ν - Real.log (1 - ‖bt‖ ^ 2) := by
          rw [← hbb, ← hbtb]; exact hmin
        have h4 : 2 * ((1 - δ) * Real.log (ρ - ε) + δ * Real.log (1 - ‖b‖))
            ≤ 2 * ∫ ξ, Real.log ‖b - ξ‖ ∂ν :=
          mul_le_mul_of_nonneg_left hAb (by norm_num)
        have h5 : 2 * ∫ ξ, Real.log ‖bt - ξ‖ ∂ν
            ≤ 2 * ((1 - δ) * Real.log (2 * ε) + δ * Real.log 2) :=
          mul_le_mul_of_nonneg_left hAt (by norm_num)
        linarith [hmin', h4, h5]
      have h6 : Real.log (1 - ‖b‖) - 2 * δ * Real.log (1 - ‖b‖) ≤ 0 := by
        have h7 : (1 - 2 * δ) * Real.log (1 - ‖b‖) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [hδle])
            (Real.log_nonpos hb0.le (by linarith [norm_nonneg b]))
        nlinarith [h7]
      have helm : -Real.log (1 - ‖bt‖ ^ 2) + Real.log (1 - ‖b‖ ^ 2)
          - 2 * δ * Real.log (1 - ‖b‖) ≤ -Real.log ε + Real.log 2 := by
        linarith [hC, hCt, h6]
      linarith [h3, helm]
    -- divide by `2 (1 - δ)`
    have hden : 0 < 2 * (1 - δ) := by linarith
    have hstep : 2 * (1 - δ) * Real.log (2 * ε) + 2 * δ * Real.log 2 - Real.log ε + Real.log 2
        ≤ 2 * (1 - δ) * (2 * Real.log 2 + (1 / 3) * Real.log ε) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hε0)]
      have h1 : (4 * δ - 1) * (Real.log 2 - (1 / 3) * Real.log ε) ≤ 0 := by
        refine mul_nonpos_of_nonpos_of_nonneg (by linarith [hδle]) ?_
        have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h3 : Real.log ε ≤ 0 := Real.log_nonpos hε0.le hε1
        linarith
      nlinarith [h1]
    have hfinal : Real.log (ρ - ε) ≤ 2 * Real.log 2 + (1 / 3) * Real.log ε := by
      have h7 : 2 * (1 - δ) * Real.log (ρ - ε)
          ≤ 2 * (1 - δ) * (2 * Real.log 2 + (1 / 3) * Real.log ε) := by linarith [hkey, hstep]
      exact le_of_mul_le_mul_left h7 hden
    -- exponentiate
    have htarget : Real.log (ρ - ε) ≤ Real.log (4 * ε ^ (1 / 3 : ℝ)) := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h5 : Real.log (ε ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log ε := Real.log_rpow hε0 _
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hε0 _)), h4, h5]
      linarith
    have hfin : ρ - ε ≤ 4 * ε ^ (1 / 3 : ℝ) :=
      (Real.log_le_log_iff hρε (by positivity)).mp htarget
    have h8 : (0:ℝ) ≤ ε ^ (1 / 3 : ℝ) := Real.rpow_nonneg hε0.le _
    linarith

section Boundary

variable {φ : E n → E n}

/-- Boundary continuity of the natural map, in `ε`-`δ` form: if `κ u` is close to `ξ ∈ Sph n`
then `κ (natMap φ u)` is close to `φ ξ`. -/
lemma boundary_control (hn : 2 ≤ n) (hV : VisualProp n) (hB : BaryProp n)
    (hφbij : Set.BijOn φ (Sph n) (Sph n)) (hφc : ContinuousOn φ (Sph n))
    (ξ : E n) (hξ : ξ ∈ Sph n) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ δ > 0, ∀ u : E n, ‖kappa u - ξ‖ < δ → ‖kappa (natMap φ u) - φ ξ‖ < ε' := by
  set ε₁ := min ε' 1 with hε₁def
  have hε₁0 : 0 < ε₁ := lt_min hε' one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε' : ε₁ ≤ ε' := min_le_left _ _
  set εs := (ε₁ / 32) ^ 3 with hεsdef
  have hεs0 : 0 < εs := by positivity
  have hεs1 : εs ≤ 1 := by
    rw [hεsdef]
    exact pow_le_one₀ (by positivity) (by linarith)
  have harith : εs + 8 * εs ^ (1 / 3 : ℝ) < ε₁ := by
    have h1 : εs ^ (1 / 3 : ℝ) = ε₁ / 32 := by
      rw [hεsdef, ← Real.rpow_natCast (ε₁ / 32) 3,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε₁ / 32)]
      norm_num
    have h2 : εs ≤ ε₁ / 4 := by
      have h5 : ε₁ ^ 2 ≤ 8192 := by nlinarith [hε₁0, hε₁1]
      rw [hεsdef, div_pow, show ((32:ℝ) ^ 3) = 32768 by norm_num,
        div_le_iff₀ (by norm_num : (0:ℝ) < 32768)]
      nlinarith [h5, hε₁0]
    rw [h1]; linarith
  obtain ⟨ε'', hε''0, hε''⟩ : ∃ ε'' > 0, ∀ θ ∈ Sph n, ‖θ - ξ‖ < ε'' → ‖φ θ - φ ξ‖ < εs := by
    have h1 : φ ⁻¹' Metric.ball (φ ξ) εs ∈ 𝓝[Sph n] ξ :=
      (hφc ξ hξ) (Metric.ball_mem_nhds (φ ξ) hεs0)
    rw [Metric.mem_nhdsWithin_iff] at h1
    obtain ⟨ε'', hε''0, hε''⟩ := h1
    refine ⟨ε'', hε''0, fun θ hθ hlt => ?_⟩
    have h2 : θ ∈ Metric.ball ξ ε'' ∩ Sph n :=
      ⟨by rwa [Metric.mem_ball, dist_eq_norm], hθ⟩
    have h3 := hε'' h2
    simp only [Set.mem_preimage] at h3
    rwa [Metric.mem_ball, dist_eq_norm] at h3
  refine ⟨min (ε'' / 2) (ε'' ^ 2 / 32), lt_min (by positivity) (by positivity), fun u hu => ?_⟩
  have hδ1 : ‖kappa u - ξ‖ < ε'' / 2 := lt_of_lt_of_le hu (min_le_left _ _)
  have hδ2 : ‖kappa u - ξ‖ < ε'' ^ 2 / 32 := lt_of_lt_of_le hu (min_le_right _ _)
  have hκ : ‖kappa u - ξ‖ ≤ ε'' / 2 := le_of_lt hδ1
  have hknu : ‖kappa u‖ < 1 := norm_kappa_lt_one u
  have hbase : ((1 - ‖kappa u‖ ^ 2) / (ε'' / 2) ^ 2) ^ (n - 1) ≤ 1 / 4 := by
    have hkn : 1 - ‖kappa u‖ ^ 2 ≤ 2 * ‖kappa u - ξ‖ := by
      have h2 : ‖ξ‖ = 1 := by rw [Sph, Metric.mem_sphere, dist_eq_norm] at hξ; simpa using hξ
      have h3 : 1 - ‖kappa u‖ ≤ ‖kappa u - ξ‖ := by
        have h4 := abs_norm_sub_norm_le (kappa u) ξ
        rw [h2] at h4
        have h5 : 1 - ‖kappa u‖ ≤ |‖kappa u‖ - 1| := by
          rw [abs_sub_comm]; exact le_abs_self _
        linarith [h4, h5]
      have hfac : 1 - ‖kappa u‖ ^ 2 = (1 - ‖kappa u‖) * (1 + ‖kappa u‖) := by ring
      nlinarith [hfac, h3, hknu.le, norm_nonneg (kappa u)]
    have hb0 : 0 ≤ (1 - ‖kappa u‖ ^ 2) / (ε'' / 2) ^ 2 :=
      div_nonneg (by nlinarith [norm_nonneg (kappa u), hknu.le]) (by positivity)
    have hb1 : (1 - ‖kappa u‖ ^ 2) / (ε'' / 2) ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hkn, hδ2]
    calc ((1 - ‖kappa u‖ ^ 2) / (ε'' / 2) ^ 2) ^ (n - 1)
        ≤ (1 - ‖kappa u‖ ^ 2) / (ε'' / 2) ^ 2 :=
          pow_le_of_le_one hb0 (by linarith) (by omega)
      _ ≤ 1 / 4 := hb1
  have hconc : visual n u ((Metric.ball ξ ε'')ᶜ) ≤ ENNReal.ofReal (1 / 4) :=
    le_trans (visualConcentration n hV u ξ hξ hε''0 hκ) (ENNReal.ofReal_le_ofReal hbase)
  have hν : ((visual n u).map φ) ((Metric.ball (φ ξ) εs)ᶜ) ≤ ENNReal.ofReal (1 / 4) := by
    refine le_trans (map_visual_compl_ball hV hφc u (ξ := ξ) (η := φ ξ) (ε := εs)
      (ε' := ε'') ?_) hconc
    exact fun θ hθ hlt => hε'' θ hθ hlt
  have hbar := barConc_self n hB ((visual n u).map φ)
    (map_visual_isProbability hV hφc u)
    (map_visual_compl_sphere hV hφbij hφc u)
    (map_visual_singleton hV hφbij hφc u)
    (φ ξ) (hφbij.mapsTo hξ) (ε := εs) hεs0 hεs1 hν
  calc ‖kappa (natMap φ u) - φ ξ‖
      = ‖kappa (bar ((visual n u).map φ)) - φ ξ‖ := rfl
    _ ≤ εs + 8 * εs ^ (1 / 3 : ℝ) := hbar
    _ < ε₁ := harith
    _ ≤ ε' := hε₁ε'

end Boundary

/-! ## The continuous extension to the closed ball -/

section Extension

variable {φ : E n → E n}

/-- The extension of the natural map to the closed ball in the Poincaré-ball model:
inside the ball it is `κ ∘ F ∘ κ⁻¹`, on the boundary sphere it is `φ`. -/
def Fhat (F φ : E n → E n) (b : E n) : E n :=
  if ‖b‖ < 1 then kappa (F (kappaInv b)) else φ b

lemma Fhat_of_lt (F φ : E n → E n) {b : E n} (h : ‖b‖ < 1) :
    Fhat F φ b = kappa (F (kappaInv b)) := if_pos h

lemma Fhat_of_eq_one (F φ : E n → E n) {b : E n} (h : ‖b‖ = 1) : Fhat F φ b = φ b :=
  if_neg (by rw [h]; norm_num)

lemma Fhat_mapsTo_closedBall (F φ : E n → E n) (hφbij : Set.BijOn φ (Sph n) (Sph n)) :
    Set.MapsTo (Fhat F φ) (closedBall1 n) (closedBall1 n) := by
  intro b hb
  rw [closedBall1, Metric.mem_closedBall, dist_zero_right] at hb ⊢
  by_cases h : ‖b‖ < 1
  · rw [Fhat_of_lt F φ h]
    have := kappa_mem_ball1 (F (kappaInv b))
    rw [ball1, Metric.mem_ball, dist_zero_right] at this
    exact this.le
  · have h1 : ‖b‖ = 1 := le_antisymm hb (not_lt.mp h)
    rw [Fhat_of_eq_one F φ h1]
    have hbS : b ∈ Sph n := mem_Sph_of_norm_eq_one h1
    rw [norm_eq_one_of_mem_Sph (hφbij.mapsTo hbS)]

lemma Fhat_eq_phi (F φ : E n → E n) {b : E n} (hb : b ∈ Sph n) : Fhat F φ b = φ b :=
  Fhat_of_eq_one F φ (norm_eq_one_of_mem_Sph hb)

/-- The extension is continuous on the closed ball, given boundary control (Piece 1). -/
lemma Fhat_continuousOn (hn : 2 ≤ n) (hV : VisualProp n) (hB : BaryProp n)
    (hφbij : Set.BijOn φ (Sph n) (Sph n)) (hφc : ContinuousOn φ (Sph n))
    (hFc : Continuous (natMap φ)) :
    ContinuousOn (Fhat (natMap φ) φ) (closedBall1 n) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε' hε'
  have hb_le : ‖b‖ ≤ 1 := by
    rw [closedBall1, Metric.mem_closedBall, dist_zero_right] at hb; exact hb
  by_cases hb1 : ‖b‖ < 1
  · have hbt : b ∈ ball1 n := by rw [ball1, Metric.mem_ball, dist_zero_right]; exact hb1
    have hcont : ContinuousAt (fun x : E n => kappa (natMap φ (kappaInv x))) b :=
      continuous_kappa.continuousAt.comp
        (hFc.continuousAt.comp (continuousOn_kappaInv.continuousAt
          (Metric.isOpen_ball.mem_nhds (by rwa [ball1] at hbt : b ∈ Metric.ball 0 1))))
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont ε' hε'
    refine ⟨min δ ((1 - ‖b‖) / 2), lt_min hδ0 (by linarith), fun b' hb' hlt => ?_⟩
    have hlt1 : dist b' b < δ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt2 : ‖b'‖ < 1 := by
      have h1 : dist b' b < (1 - ‖b‖) / 2 := lt_of_lt_of_le hlt (min_le_right _ _)
      rw [dist_eq_norm] at h1
      calc ‖b'‖ ≤ ‖b' - b‖ + ‖b‖ := by
            have h2 := norm_add_le (b' - b) b
            rwa [sub_add_cancel] at h2
        _ < (1 - ‖b‖) / 2 + ‖b‖ := by linarith
        _ = (1 + ‖b‖) / 2 := by ring
        _ < 1 := by linarith
    rw [Fhat_of_lt _ _ hlt2, Fhat_of_lt _ _ hb1]
    exact hδ (x := b') hlt1
  · have hb_eq : ‖b‖ = 1 := le_antisymm hb_le (not_lt.mp hb1)
    have hbS : b ∈ Sph n := mem_Sph_of_norm_eq_one hb_eq
    rw [Fhat_of_eq_one _ _ hb_eq]
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := boundary_control hn hV hB hφbij hφc b hbS hε'
    obtain ⟨δ₂, hδ₂0, hδ₂⟩ : ∃ δ > 0, ∀ θ ∈ Sph n, dist θ b < δ →
        dist (φ θ) (φ b) < ε' := by
      have h1 : φ ⁻¹' Metric.ball (φ b) ε' ∈ 𝓝[Sph n] b :=
        (hφc b hbS) (Metric.ball_mem_nhds (φ b) hε')
      rw [Metric.mem_nhdsWithin_iff] at h1
      obtain ⟨δ₂, hδ₂0, hδ₂⟩ := h1
      exact ⟨δ₂, hδ₂0, fun θ hθ hlt => by
        have h := hδ₂ ⟨hlt, hθ⟩
        simp only [Set.mem_preimage] at h
        rwa [Metric.mem_ball] at h⟩
    refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, fun b' hb' hlt => ?_⟩
    have hlt₁ : dist b' b < δ₁ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt₂ : dist b' b < δ₂ := lt_of_lt_of_le hlt (min_le_right _ _)
    have hb'_le : ‖b'‖ ≤ 1 := by
      rw [closedBall1, Metric.mem_closedBall, dist_zero_right] at hb'; exact hb'
    by_cases hb'1 : ‖b'‖ < 1
    · rw [Fhat_of_lt _ _ hb'1]
      have hu : kappa (kappaInv b') = b' := kappa_kappaInv b' hb'1
      have h1 : ‖kappa (kappaInv b') - b‖ < δ₁ := by
        rw [hu, ← dist_eq_norm]; exact hlt₁
      have h2 := hδ₁ (kappaInv b') h1
      rwa [dist_eq_norm]
    · have hb'eq : ‖b'‖ = 1 := le_antisymm hb'_le (not_lt.mp hb'1)
      rw [Fhat_of_eq_one _ _ hb'eq]
      exact hδ₂ b' (mem_Sph_of_norm_eq_one hb'eq) hlt₂

end Extension

/-! ## Radial projection onto the boundary sphere -/

section Radial

/-- Radial projection from `p` onto the unit sphere: the first point where the ray from `p`
through `y` meets the sphere. -/
def radialProj (p y : E n) : E n :=
  p + (-(inner ℝ p (y - p) / ‖y - p‖ ^ 2)
    + Real.sqrt ((inner ℝ p (y - p) / ‖y - p‖ ^ 2) ^ 2 + (1 - ‖p‖ ^ 2) / ‖y - p‖ ^ 2)) • (y - p)

lemma continuousAt_radialProj (p y : E n) (hy : y ≠ p) :
    ContinuousAt (fun z : E n => radialProj p z) y := by
  have hd_ne : ‖y - p‖ ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 (norm_ne_zero_iff.mpr ?_)
    exact sub_ne_zero.mpr hy
  have hsub : ContinuousAt (fun z : E n => z - p) y :=
    continuous_id.continuousAt.sub continuousAt_const
  have hd : ContinuousAt (fun z : E n => ‖z - p‖ ^ 2) y :=
    ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt).pow 2
  have hs : ContinuousAt (fun z : E n => inner ℝ p (z - p) / ‖z - p‖ ^ 2) y :=
    (continuous_const.inner (continuous_id.sub continuous_const)).continuousAt.div hd hd_ne
  have hr : ContinuousAt (fun z : E n =>
      Real.sqrt ((inner ℝ p (z - p) / ‖z - p‖ ^ 2) ^ 2 + (1 - ‖p‖ ^ 2) / ‖z - p‖ ^ 2)) y :=
    Real.continuous_sqrt.continuousAt.comp
      ((hs.pow 2).add (continuousAt_const.div hd hd_ne))
  have h2 : ContinuousAt (fun z : E n =>
      (-(inner ℝ p (z - p) / ‖z - p‖ ^ 2)
        + Real.sqrt ((inner ℝ p (z - p) / ‖z - p‖ ^ 2) ^ 2
          + (1 - ‖p‖ ^ 2) / ‖z - p‖ ^ 2)) • (z - p)) y :=
    (hs.neg.add hr).smul hsub
  exact continuousAt_const.add (by simpa only [radialProj] using h2)

lemma continuousOn_radialProj (p : E n) :
    ContinuousOn (fun y : E n => radialProj p y) {p}ᶜ := by
  intro y hy
  exact (continuousAt_radialProj p y (by simpa using hy)).continuousWithinAt

lemma norm_radialProj (p y : E n) (hp : ‖p‖ < 1) (hy : y ≠ p) : ‖radialProj p y‖ = 1 := by
  set d := y - p with hddef
  set s := inner ℝ p d / ‖d‖ ^ 2 with hsdef
  set r := Real.sqrt (s ^ 2 + (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2) with hrdef
  have hd0 : (0:ℝ) < ‖d‖ := by
    rw [hddef]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  have hd2 : (0:ℝ) < ‖d‖ ^ 2 := by positivity
  have hX : 0 ≤ s ^ 2 + (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 := by
    have : (0:ℝ) < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
    positivity
  have hr2 : r ^ 2 = s ^ 2 + (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 := by rw [hrdef, Real.sq_sqrt hX]
  have hsdf : inner ℝ p d = s * ‖d‖ ^ 2 := by
    rw [hsdef]; field_simp [ne_of_gt hd2]
  have key : (-s + r) ^ 2 + 2 * s * (-s + r) = (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 := by
    nlinarith [hr2]
  have key' : ((-s + r) ^ 2 + 2 * s * (-s + r)) * ‖d‖ ^ 2 = 1 - ‖p‖ ^ 2 := by
    rw [key]; field_simp [ne_of_gt hd2]
  have hnorm : ‖p + (-s + r) • d‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hsdf]
    nlinarith [key', hd2, norm_nonneg p]
  have h1 : ‖radialProj p y‖ ^ 2 = 1 := by
    rw [radialProj]
    simpa only [hddef, hsdef, hrdef] using hnorm
  nlinarith [norm_nonneg (radialProj p y)]

lemma radialProj_self (p y : E n) (hp : ‖p‖ < 1) (hy : y ∈ Sph n) : radialProj p y = y := by
  set d := y - p with hddef
  set s := inner ℝ p d / ‖d‖ ^ 2 with hsdef
  have hd0 : (0:ℝ) < ‖d‖ := by
    rw [hddef]
    have hne : y - p ≠ 0 := by
      intro h
      have h1 : y = p := sub_eq_zero.mp h
      rw [h1] at hy
      have := norm_eq_one_of_mem_Sph hy
      linarith
    exact norm_pos_iff.mpr hne
  have hd2 : (0:ℝ) < ‖d‖ ^ 2 := by positivity
  have hny : ‖y‖ = 1 := norm_eq_one_of_mem_Sph hy
  have hnorm : ‖d‖ ^ 2 + 2 * inner ℝ p d = 1 - ‖p‖ ^ 2 := by
    rw [hddef, norm_sub_sq_real, hny, real_inner_comm p y, inner_sub_right,
      real_inner_self_eq_norm_sq]
    ring
  have h2s : 1 + 2 * s = (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 := by
    rw [hsdef]; field_simp [ne_of_gt hd2]; linarith [hnorm]
  have hsq : s ^ 2 + (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 = (1 + s) ^ 2 := by rw [← h2s]; ring
  have h1s : 0 ≤ 1 + s := by
    have hpos : (0:ℝ) < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
    have h2 : 1 + s = ((1 - ‖p‖ ^ 2) / ‖d‖ ^ 2 + 1) / 2 := by linarith [h2s]
    rw [h2]; positivity
  have hsqrt : Real.sqrt (s ^ 2 + (1 - ‖p‖ ^ 2) / ‖d‖ ^ 2) = 1 + s := by
    rw [hsq, Real.sqrt_sq h1s]
  rw [radialProj]
  rw [← hddef, ← hsdef, hsqrt]
  rw [show -s + (1 + s) = 1 by ring, one_smul, hddef]
  abel

end Radial

/-! ## Assembly: the natural map is onto -/

section Assembly

theorem natMapSurj (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hV : VisualProp n) (hB : BaryProp n) (hJ : NatMapJacProp n) : NatMapSurjProp n := by
  classical
  intro φ hφbij hφc
  have hn2 : 2 ≤ n := by omega
  have hFc : Continuous (natMap φ) := (hJ φ hφbij hφc).1.continuous
  -- the boundary map as a homeomorphism of the sphere
  have hmap : ∀ x : ↥(Sph n), φ (x : E n) ∈ Sph n :=
    fun x => hφbij.mapsTo x.2
  let g : ↥(Sph n) → ↥(Sph n) := fun x => ⟨φ (x : E n), hmap x⟩
  have hgc : Continuous g := by
    have h1 : Continuous (fun x : ↥(Sph n) => φ (x : E n)) :=
      continuousOn_iff_continuous_domRestrict.mp hφc
    exact Continuous.subtype_mk h1 hmap
  have hgb : Function.Bijective g := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h1 : φ (x : E n) = φ (y : E n) := congrArg Subtype.val hxy
      exact Subtype.ext (hφbij.injOn x.2 y.2 h1)
    · obtain ⟨w, hw, hwy⟩ := hφbij.surjOn y.2
      exact ⟨⟨w, hw⟩, Subtype.ext hwy⟩
  haveI : CompactSpace ↥(Sph n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E n) 1)
  let e : ↥(Sph n) ≃ₜ ↥(Sph n) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb) hgc
  -- a continuous left inverse of `φ` on the sphere
  let ψ : E n → E n :=
    fun y => if h : y ∈ Sph n then ((e.symm ⟨y, h⟩ : ↥(Sph n)) : E n) else y
  have hψ_apply : ∀ (y : E n) (h : y ∈ Sph n),
      ψ y = ((e.symm ⟨y, h⟩ : ↥(Sph n)) : E n) := fun y h => dif_pos h
  have hψ_cont : ContinuousOn ψ (Sph n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Sph n).domRestrict ψ = fun x => ((e.symm x : ↥(Sph n)) : E n) := by
      funext x
      exact hψ_apply (x : E n) x.2
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  have hψ_inv : ∀ x ∈ Sph n, ψ (φ x) = x := by
    intro x hx
    have hx' : φ x ∈ Sph n := hφbij.mapsTo hx
    rw [hψ_apply (φ x) hx']
    have h2 : e ⟨x, hx⟩ = ⟨φ x, hx'⟩ := Subtype.ext rfl
    rw [← h2, e.symm_apply_apply]
  -- the natural map is onto the open ball
  have key : ∀ b ∈ ball1 n, ∃ u : E n, natMap φ u = kappaInv b := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, hpno⟩ := hcon
    have hp1 : ‖p‖ < 1 := by rw [ball1, Metric.mem_ball, dist_zero_right] at hp; exact hp
    have hmiss : ∀ b ∈ closedBall1 n, Fhat (natMap φ) φ b ≠ p := by
      intro b hb
      rw [closedBall1, Metric.mem_closedBall, dist_zero_right] at hb
      by_cases hb1 : ‖b‖ < 1
      · rw [Fhat_of_lt _ _ hb1]
        intro h
        have h2 : natMap φ (kappaInv b) = kappaInv p := by
          have h3 : kappa (kappaInv p) = p := kappa_kappaInv p hp1
          rw [← h3] at h
          exact kappa_injective h
        exact hpno (kappaInv b) h2
      · have hbeq : ‖b‖ = 1 := le_antisymm hb (not_lt.mp hb1)
        rw [Fhat_of_eq_one _ _ hbeq]
        intro h
        have hbS : b ∈ Sph n := mem_Sph_of_norm_eq_one hbeq
        have h2 := hφbij.mapsTo hbS
        rw [h] at h2
        have h3 : ‖p‖ = 1 := norm_eq_one_of_mem_Sph h2
        linarith
    have hFhat_c : ContinuousOn (Fhat (natMap φ) φ) (closedBall1 n) :=
      Fhat_continuousOn hn2 hV hB hφbij hφc hFc
    have hFhat_m : Set.MapsTo (Fhat (natMap φ) φ) (closedBall1 n) (closedBall1 n) :=
      Fhat_mapsTo_closedBall _ _ hφbij
    have hRad_c : ContinuousOn (fun b => radialProj p (Fhat (natMap φ) φ b)) (closedBall1 n) :=
      (continuousOn_radialProj p).comp hFhat_c
        (fun b hb => by simpa using hmiss b hb)
    have hr_c : ContinuousOn (fun b => ψ (radialProj p (Fhat (natMap φ) φ b)))
        (closedBall1 n) :=
      hψ_cont.comp hRad_c (fun b hb => mem_Sph_of_norm_eq_one
        (norm_radialProj p _ hp1 (by simpa using hmiss b hb)))
    have hr_m : Set.MapsTo (fun b => ψ (radialProj p (Fhat (natMap φ) φ b)))
        (closedBall1 n) (Sph n) := by
      intro b hb
      have h1 : radialProj p (Fhat (natMap φ) φ b) ∈ Sph n := mem_Sph_of_norm_eq_one
        (norm_radialProj p _ hp1 (by simpa using hmiss b hb))
      change ψ (radialProj p (Fhat (natMap φ) φ b)) ∈ Sph n
      rw [hψ_apply _ h1]
      exact (e.symm ⟨_, h1⟩).2
    have hr_id : ∀ x ∈ Sph n, ψ (radialProj p (Fhat (natMap φ) φ x)) = x := by
      intro x hx
      have h1 : Fhat (natMap φ) φ x = φ x := Fhat_eq_phi _ _ hx
      rw [h1]
      have h2 : φ x ∈ Sph n := hφbij.mapsTo hx
      rw [radialProj_self p (φ x) hp1 h2]
      exact hψ_inv x hx
    obtain ⟨f, hfC, hfm, hfid⟩ :=
      smoothRetraction n (by omega) _ hr_c hr_m hr_id
    exact noRetractionSmooth n (by omega) ⟨f, hfC, hfm, hfid⟩
  -- hence the natural map is onto
  intro y
  obtain ⟨u, hu⟩ := key (kappa y) (kappa_mem_ball1 y)
  exact ⟨u, by rw [hu, kappaInv_kappa]⟩

end Assembly


end

end Work.Mostow
