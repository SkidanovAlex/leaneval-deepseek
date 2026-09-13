import Mathlib
import Submission.Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere
import Submission.Commons.Analysis.Analytic.ring_choose_bound

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators NNReal ENNReal

local notation "euc" n:max => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000

noncomputable section

namespace Commons.Analysis.Harmonic

/-! ## The power series of the Poisson kernel -/

section KernelSeries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear functional `v ↦ 2⟪p₀, v⟫/a`. -/
noncomputable def linCoeff (p₀ : E) (a : ℝ) : E →L[ℝ] ℝ := (2 / a) • innerSL ℝ p₀

/-- The bilinear form `(v,w) ↦ ⟪v,w⟫/a`. -/
noncomputable def bilCoeff (a : ℝ) : E →L[ℝ] (E →L[ℝ] ℝ) := a⁻¹ • innerSL ℝ

/-- The quadratic polynomial `v ↦ (2⟪p₀,v⟫ + ‖v‖²)/a`. -/
noncomputable def quadFun (p₀ : E) (a : ℝ) (v : E) : ℝ :=
  (2 * inner ℝ p₀ v + ‖v‖ ^ 2) / a

/-- The formal power series of `quadFun p₀ a` at `0`. -/
noncomputable def quadSeries (p₀ : E) (a : ℝ) : FormalMultilinearSeries ℝ E ℝ
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 ℝ E ℝ).symm (linCoeff p₀ a)
  | 2 => ContinuousMultilinearMap.uncurryRight
          ((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).symm (bilCoeff a))
  | _ => 0

@[simp] lemma quadSeries_zero (p₀ : E) (a : ℝ) : quadSeries p₀ a 0 = 0 := rfl
lemma quadSeries_one (p₀ : E) (a : ℝ) :
    quadSeries p₀ a 1 = (continuousMultilinearCurryFin1 ℝ E ℝ).symm (linCoeff p₀ a) := rfl
lemma quadSeries_two (p₀ : E) (a : ℝ) :
    quadSeries p₀ a 2 = ContinuousMultilinearMap.uncurryRight
          ((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).symm (bilCoeff a)) := rfl
@[simp] lemma quadSeries_large (p₀ : E) (a : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    quadSeries p₀ a n = 0 := by
  rcases n with _|_|_|n
  · omega
  · omega
  · omega
  · rfl

lemma quadSeries_one_apply (p₀ : E) (a : ℝ) (v : E) :
    quadSeries p₀ a 1 (fun _ : Fin 1 => v) = (2 / a) * inner ℝ p₀ v := by
  rw [quadSeries_one, continuousMultilinearCurryFin1_symm_apply]
  show ((2 / a) • innerSL ℝ p₀) v = (2 / a) * inner ℝ p₀ v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

lemma quadSeries_two_apply (p₀ : E) (a : ℝ) (v : E) :
    quadSeries p₀ a 2 (fun _ : Fin 2 => v) = a⁻¹ * ‖v‖ ^ 2 := by
  rw [quadSeries_two]
  simp only [ContinuousMultilinearMap.uncurryRight_apply, continuousMultilinearCurryFin1_symm_apply]
  show ((bilCoeff a) v) v = a⁻¹ * ‖v‖ ^ 2
  simp only [bilCoeff, smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply ℝ v v, real_inner_self_eq_norm_sq]

/-- `HasSum` of a sequence vanishing beyond index `2`. -/
lemma hasSum_of_eq_zero_of_three {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {f : ℕ → M} (h : ∀ n, 3 ≤ n → f n = 0) :
    HasSum f (f 0 + f 1 + f 2) := by
  set g : ℕ → M := fun n => (if n = 0 then f 0 else 0) + (if n = 1 then f 1 else 0)
      + (if n = 2 then f 2 else 0) with hg
  have hfg : f = g := by
    funext n
    rcases lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp [hg]
    · have hfn : f n = 0 := h n hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      simp [hg, hfn, h0, h1, h2]
  have h0 : HasSum (fun n : ℕ => if n = 0 then f 0 else 0) (f 0) :=
    hasSum_single 0 (fun b hb => by simp [hb])
  have h1 : HasSum (fun n : ℕ => if n = 1 then f 1 else 0) (f 1) :=
    hasSum_single 1 (fun b hb => by simp [hb])
  have h2 : HasSum (fun n : ℕ => if n = 2 then f 2 else 0) (f 2) :=
    hasSum_single 2 (fun b hb => by simp [hb])
  have hsum : HasSum g (g 0 + g 1 + g 2) := by
    have hval : g 0 + g 1 + g 2 = f 0 + f 1 + f 2 := by simp [hg]
    rw [hval]
    have hh := (h0.add h1).add h2
    simpa [hg] using hh
  rwa [hfg]

lemma quadSeries_hasSum (p₀ : E) (a : ℝ) (v : E) :
    HasSum (fun n : ℕ => quadSeries p₀ a n (fun _ => v)) (quadFun p₀ a v) := by
  have h3 : ∀ n, 3 ≤ n → quadSeries p₀ a n (fun _ => v) = 0 := by
    intro n hn; rw [quadSeries_large p₀ a hn]; rfl
  have hthis := hasSum_of_eq_zero_of_three h3
  have hval : ((quadSeries p₀ a 0) (fun _ => v) + (quadSeries p₀ a 1) (fun _ => v))
        + (quadSeries p₀ a 2) (fun _ => v) = quadFun p₀ a v := by
    rw [quadSeries_zero, quadSeries_one_apply, quadSeries_two_apply, quadFun]
    simp only [zero_apply, zero_add]
    ring
  rw [hval] at hthis
  exact hthis

lemma quadSeries_radius_ge_one (p₀ : E) (a : ℝ) :
    (1 : ℝ≥0∞) ≤ (quadSeries p₀ a).radius := by
  set C : ℝ := max 1 (max ‖quadSeries p₀ a 1‖ ‖quadSeries p₀ a 2‖) with hC
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_left 1 _)
  have hC1 : ‖quadSeries p₀ a 1‖ ≤ C := le_trans (le_max_left _ _) (le_max_right 1 _)
  have hC2 : ‖quadSeries p₀ a 2‖ ≤ C := le_trans (le_max_right _ _) (le_max_right 1 _)
  refine FormalMultilinearSeries.le_radius_of_bound _ C (fun n => ?_)
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · simpa using hC0
    · simpa using hC1
    · simpa using hC2
  · rw [quadSeries_large p₀ a hn, norm_zero]
    simpa using hC0

lemma hasFPowerSeriesAt_quadFun (p₀ : E) (a : ℝ) :
    HasFPowerSeriesAt (quadFun p₀ a) (quadSeries p₀ a) 0 := by
  refine ⟨1, quadSeries_radius_ge_one p₀ a, one_pos, fun {y} _ => ?_⟩
  rw [zero_add]
  simpa using quadSeries_hasSum p₀ a y

/-- `x ↦ (1+x)^α` is analytic at every point `s > -1`. -/
lemma analyticAt_one_add_rpow (α : ℝ) {s : ℝ} (hs : -1 < s) :
    AnalyticAt ℝ (fun x : ℝ => (1 + x) ^ α) s := by
  have hpos : (0:ℝ) < 1 + s := by linarith
  have hlog : AnalyticAt ℝ (fun x : ℝ => Real.log (1 + x)) s := by
    apply AnalyticAt.log _ hpos
    fun_prop
  have hmul : AnalyticAt ℝ (fun x : ℝ => Real.log (1 + x) * α) s := by
    have heq : (fun x : ℝ => Real.log (1 + x) * α) = fun x : ℝ => α • Real.log (1 + x) := by
      ext x; rw [smul_eq_mul, mul_comm]
    rw [heq]
    exact AnalyticAt.const_smul (c := α) hlog
  have hexp : AnalyticAt ℝ (fun t : ℝ => Real.exp t) (Real.log (1 + s) * α) := by
    have h := NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := ℝ) (Real.log (1 + s) * α)
    rwa [Real.exp_eq_exp_ℝ.symm] at h
  have hcomp := AnalyticAt.comp (f := fun x : ℝ => Real.log (1 + x) * α) (x := s) hexp hmul
  refine AnalyticAt.congr hcomp ?_
  filter_upwards [isOpen_Ioi.mem_nhds (show (-1:ℝ) < s by linarith)] with x hx
  rw [mem_Ioi] at hx
  exact (Real.rpow_def_of_pos (by linarith : (0:ℝ) < 1 + x) α).symm

/-- The power series of `v ↦ (1 + quadFun p₀ a v)^α`. -/
noncomputable def extSeries (p₀ : E) (a α : ℝ) : FormalMultilinearSeries ℝ E ℝ :=
  (binomialSeries ℝ α).comp (quadSeries p₀ a)

lemma norm_binomialSeries (α : ℝ) (n : ℕ) : ‖binomialSeries ℝ α n‖ = |Ring.choose α n| := by
  rw [binomialSeries, FormalMultilinearSeries.ofScalars, norm_smul, Real.norm_eq_abs,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]

lemma extSeries_hasFPowerSeriesAt (p₀ : E) (a α : ℝ) :
    HasFPowerSeriesAt (fun v : E => (1 + quadFun p₀ a v) ^ α) (extSeries p₀ a α) 0 := by
  have h0 : quadFun p₀ a 0 = 0 := by simp [quadFun]
  have hg : HasFPowerSeriesAt (fun x : ℝ => (1 + x) ^ α) (binomialSeries ℝ α)
      (quadFun p₀ a 0) := by
    rw [h0]
    exact Real.one_add_rpow_hasFPowerSeriesAt_zero (a := α)
  have hf := hasFPowerSeriesAt_quadFun p₀ a
  have hcomp := hg.comp hf
  simpa [Function.comp_def, extSeries] using hcomp

lemma norm_extSeries_le (p₀ : E) (a α : ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hα : ∀ n, |Ring.choose α n| ≤ C ^ n) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ d, ‖extSeries p₀ a α d‖ ≤ D ^ d := by
  set A : ℝ := max 1 (max ‖quadSeries p₀ a 1‖ ‖quadSeries p₀ a 2‖) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hq1 : ‖quadSeries p₀ a 1‖ ≤ A := le_trans (le_max_left _ _) (le_max_right 1 _)
  have hq2 : ‖quadSeries p₀ a 2‖ ≤ A := le_trans (le_max_right _ _) (le_max_right 1 _)
  have hA2 : A ≤ A ^ 2 := by
    calc A = A * 1 := by ring
      _ ≤ A * A := by gcongr
      _ = A ^ 2 := by ring
  have hq : ∀ j : ℕ, ‖quadSeries p₀ a j‖ ≤ A ^ j := by
    intro j
    rcases lt_or_ge j 3 with hj | hj
    · interval_cases j
      · rw [quadSeries_zero, norm_zero]; positivity
      · simpa using hq1
      · exact le_trans hq2 hA2
    · rw [quadSeries_large p₀ a hj, norm_zero]
      positivity
  refine ⟨2 * C * A, ?_, fun d => ?_⟩
  · nlinarith [hC, hA1]
  · calc ‖extSeries p₀ a α d‖
        = ‖∑ c : Composition d, (binomialSeries ℝ α).compAlongComposition (quadSeries p₀ a) c‖ :=
          rfl
      _ ≤ ∑ c : Composition d, ‖(binomialSeries ℝ α).compAlongComposition (quadSeries p₀ a) c‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Composition d, C ^ d * A ^ d := by
          refine Finset.sum_le_sum fun c _ => ?_
          refine le_trans (FormalMultilinearSeries.compAlongComposition_norm _ _ c) ?_
          rw [norm_binomialSeries]
          have h1 : |Ring.choose α c.length| ≤ C ^ d :=
            le_trans (hα c.length) (pow_le_pow_right₀ hC c.length_le)
          have h2 : ∏ i, ‖quadSeries p₀ a (c.blocksFun i)‖ ≤ A ^ d := by
            refine le_trans (Finset.prod_le_prod (fun i _ => norm_nonneg _)
              (fun i _ => hq _)) ?_
            rw [Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (Fintype.card (Composition d) : ℝ) * (C ^ d * A ^ d) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (2 : ℝ) ^ (d - 1) * (C ^ d * A ^ d) := by
          rw [composition_card]; push_cast; ring
      _ ≤ (2 * C * A) ^ d := by
          have h2d : (2:ℝ) ^ (d - 1) ≤ 2 ^ d :=
            pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
          have hthis := mul_le_mul_of_nonneg_right h2d (by positivity : (0:ℝ) ≤ C ^ d * A ^ d)
          calc (2:ℝ) ^ (d - 1) * (C ^ d * A ^ d) ≤ 2 ^ d * (C ^ d * A ^ d) := hthis
            _ = (2 * C * A) ^ d := by rw [mul_pow, mul_pow]; ring

/-- The bilinear form `⟪·,·⟫` as a continuous multilinear map. -/
noncomputable def innerBilin : E [×2]→L[ℝ] ℝ :=
  ContinuousMultilinearMap.uncurryRight
    ((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).symm (innerSL ℝ))

lemma innerBilin_apply (v : E) : innerBilin (fun _ : Fin 2 => v) = ‖v‖ ^ 2 := by
  rw [innerBilin,
    ContinuousMultilinearMap.uncurryRight_apply, continuousMultilinearCurryFin1_symm_apply]
  show ((innerSL ℝ) v) v = ‖v‖ ^ 2
  rw [innerSL_apply_apply ℝ v v, real_inner_self_eq_norm_sq]

lemma analyticAt_norm_sq (v₀ : E) : AnalyticAt ℝ (fun v : E => ‖v‖ ^ 2) v₀ := by
  have h1 : AnalyticAt ℝ (innerBilin : (Fin 2 → E) → ℝ) (fun _ : Fin 2 => v₀) :=
    ContinuousMultilinearMap.analyticAt innerBilin
  have h2 : AnalyticAt ℝ (fun v : E => (fun _ : Fin 2 => v)) v₀ :=
    (ContinuousLinearMap.pi (fun _ : Fin 2 => ContinuousLinearMap.id ℝ E)).analyticAt v₀
  have h3 : AnalyticAt ℝ
      ((innerBilin : (Fin 2 → E) → ℝ) ∘ (fun v : E => (fun _ : Fin 2 => v))) v₀ :=
    AnalyticAt.comp h1 h2
  refine AnalyticAt.congr h3 ?_
  filter_upwards with v
  simp only [Function.comp_def, innerBilin_apply]

lemma analyticAt_quadFun (p₀ : E) (a : ℝ) (v₀ : E) :
    AnalyticAt ℝ (fun v : E => quadFun p₀ a v) v₀ := by
  have h1 : AnalyticAt ℝ (fun v : E => inner ℝ p₀ v) v₀ := (innerSL ℝ p₀).analyticAt v₀
  have h2 : AnalyticAt ℝ (fun v : E => ‖v‖ ^ 2) v₀ := analyticAt_norm_sq v₀
  have h3 : AnalyticAt ℝ (fun v : E => 2 * inner ℝ p₀ v + ‖v‖ ^ 2) v₀ := by
    have ha : AnalyticAt ℝ (fun v : E => 2 * inner ℝ p₀ v) v₀ := by
      have hh := AnalyticAt.const_smul (c := (2:ℝ)) h1
      convert hh using 1
      ext v; rw [Pi.smul_apply, smul_eq_mul]
    exact ha.add h2
  have h4 : AnalyticAt ℝ (fun v : E => (2 * inner ℝ p₀ v + ‖v‖ ^ 2) / a) v₀ :=
    AnalyticAt.div_const (c := a) h3
  simpa [quadFun] using h4

lemma analyticAt_one_add_quadFun (p₀ : E) (a α : ℝ) {v₀ : E} (hv : -1 < quadFun p₀ a v₀) :
    AnalyticAt ℝ (fun v : E => (1 + quadFun p₀ a v) ^ α) v₀ :=
  (analyticAt_one_add_rpow α hv).comp (analyticAt_quadFun p₀ a v₀)

lemma le_radius_extSeries (p₀ : E) (a α : ℝ) {D : ℝ} (hD1 : 1 ≤ D)
    (hbound : ∀ d, ‖extSeries p₀ a α d‖ ≤ D ^ d) {r : ℝ≥0} (hr : (r : ℝ) = 1 / D) :
    (r : ℝ≥0∞) ≤ (extSeries p₀ a α).radius := by
  have hDpos : (0:ℝ) < D := lt_of_lt_of_le zero_lt_one hD1
  refine FormalMultilinearSeries.le_radius_of_bound (extSeries p₀ a α) (r := r) 1 (fun n => ?_)
  rw [hr]
  calc ‖extSeries p₀ a α n‖ * (1 / D) ^ n ≤ D ^ n * (1 / D) ^ n := by
        refine mul_le_mul_of_nonneg_right (hbound n) ?_
        positivity
    _ = 1 := by
        rw [← mul_pow, mul_one_div_cancel (ne_of_gt hDpos), one_pow]

lemma extSeries_sum_eq (p₀ : E) (a α : ℝ) {ρ : ℝ≥0} (hρ : 0 < ρ) {D : ℝ} (hD1 : 1 ≤ D)
    (hbound : ∀ d, ‖extSeries p₀ a α d‖ ≤ D ^ d) (hρD : (ρ : ℝ) ≤ 1 / D)
    (han : ∀ v : E, ‖v‖ < (ρ : ℝ) → -1 < quadFun p₀ a v) :
    ∀ v : E, ‖v‖ < (ρ : ℝ) → (1 + quadFun p₀ a v) ^ α = (extSeries p₀ a α).sum v := by
  have hDpos : (0:ℝ) < D := lt_of_lt_of_le zero_lt_one hD1
  have hnn : (0:ℝ) ≤ 1 / D := div_nonneg zero_le_one hDpos.le
  set r : ℝ≥0 := ⟨(1 / D : ℝ), hnn⟩ with hr
  have hrR : (r : ℝ) = 1 / D := rfl
  have hrad : (r : ℝ≥0∞) ≤ (extSeries p₀ a α).radius :=
    le_radius_extSeries p₀ a α hD1 hbound hrR
  have hρr : ρ ≤ r := by
    have h1 : (ρ : ℝ) ≤ (r : ℝ) := by rw [hrR]; exact hρD
    exact_mod_cast h1
  have hradρ : (ρ : ℝ≥0∞) ≤ (extSeries p₀ a α).radius :=
    (ENNReal.coe_le_coe.mpr hρr).trans hrad
  have hρpos : (0 : ℝ≥0∞) < ρ := ENNReal.coe_pos.mpr hρ
  have hpos_rad : 0 < (extSeries p₀ a α).radius := lt_of_lt_of_le hρpos hradρ
  have h2 : HasFPowerSeriesOnBall (extSeries p₀ a α).sum (extSeries p₀ a α) 0
      (extSeries p₀ a α).radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall _ hpos_rad
  obtain ⟨r1, hr1⟩ := extSeries_hasFPowerSeriesAt p₀ a α
  set r' : ℝ≥0∞ := min r1 (extSeries p₀ a α).radius with hr'
  have hr'pos : 0 < r' := lt_min hr1.r_pos h2.r_pos
  have huniq : EqOn (fun v : E => (1 + quadFun p₀ a v) ^ α) (extSeries p₀ a α).sum
      (eball 0 r') :=
    HasFPowerSeriesOnBall.unique (hr1.mono hr'pos (min_le_left _ _))
      (h2.mono hr'pos (min_le_right _ _))
  have heq_near : (fun v : E => (1 + quadFun p₀ a v) ^ α) =ᶠ[𝓝 (0:E)] (extSeries p₀ a α).sum :=
    Filter.eventuallyEq_of_mem (Metric.eball_mem_nhds 0 hr'pos) huniq
  have han1 : AnalyticOnNhd ℝ (fun v : E => (1 + quadFun p₀ a v) ^ α)
      (eball 0 (ρ:ℝ≥0∞)) :=
    fun v hv => analyticAt_one_add_quadFun p₀ a α (han v (by
      rwa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe,
        ← NNReal.coe_lt_coe, coe_nnnorm] at hv))
  have han2 : AnalyticOnNhd ℝ (extSeries p₀ a α).sum (eball 0 (ρ:ℝ≥0∞)) :=
    (extSeries p₀ a α).analyticOnNhd.mono
      (Metric.eball_subset_eball hradρ)
  have hconn : IsPreconnected (eball (0:E) (ρ:ℝ≥0∞)) := (isConnected_eball hρpos).isPreconnected
  have hz0 : (0:E) ∈ eball (0:E) (ρ:ℝ≥0∞) := by rw [Metric.mem_eball, edist_self]; exact hρpos
  have hmain := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq han1 han2 hconn hz0 heq_near
  intro v hv
  exact hmain (by rwa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe,
    ← NNReal.coe_lt_coe, coe_nnnorm])

section NormBounds

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma norm_linCoeff_le (p₀ : F) {a δ : ℝ} (ha : a = ‖p₀‖ ^ 2) (hδ : 0 < δ)
    (hδp : δ ≤ ‖p₀‖) : ‖linCoeff p₀ a‖ ≤ 2 / δ := by
  have hnorm : (0:ℝ) < ‖p₀‖ := lt_of_lt_of_le hδ hδp
  rw [ha]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [linCoeff, smul_apply, smul_eq_mul, innerSL_apply_apply, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < 2 / ‖p₀‖ ^ 2)]
  calc (2 / ‖p₀‖ ^ 2) * |⟪p₀, v⟫_ℝ|
      ≤ (2 / ‖p₀‖ ^ 2) * (‖p₀‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm p₀ v) (by positivity)
    _ = (2 / ‖p₀‖) * ‖v‖ := by field_simp
    _ ≤ (2 / δ) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hδ hδp) (norm_nonneg v)

lemma norm_bilCoeff_le {a δ : ℝ} (hδ2 : δ ^ 2 ≤ a) (hδ : 0 < δ) :
    ‖bilCoeff (a := a) (E := F)‖ ≤ 1 / δ ^ 2 := by
  have hδ2pos : (0:ℝ) < δ ^ 2 := by positivity
  have hapos : (0:ℝ) < a := lt_of_lt_of_le hδ2pos hδ2
  have hinvnn : (0:ℝ) ≤ a⁻¹ := inv_nonneg.mpr hapos.le
  have hinv : a⁻¹ ≤ 1 / δ ^ 2 := by
    rw [one_div, inv_le_inv₀ hapos hδ2pos]; exact hδ2
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v : F => ?_)
  rw [bilCoeff, smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinvnn]
  rw [show ‖((innerSL ℝ : F →L[ℝ] (F →L[ℝ] ℝ)) v)‖ = ‖v‖ from
    LinearIsometry.norm_map (InnerProductSpace.toDualMap ℝ F) v]
  exact mul_le_mul_of_nonneg_right hinv (norm_nonneg v)

lemma norm_quadSeries_one_le (p₀ : F) {a δ : ℝ} (ha : a = ‖p₀‖ ^ 2) (hδ : 0 < δ)
    (hδp : δ ≤ ‖p₀‖) : ‖quadSeries p₀ a 1‖ ≤ 2 / δ := by
  rw [quadSeries_one]
  rw [LinearIsometryEquiv.norm_map]
  exact norm_linCoeff_le p₀ ha hδ hδp

lemma norm_quadSeries_two_le (p₀ : F) {a δ : ℝ} (ha : a = ‖p₀‖ ^ 2) (hδ : 0 < δ)
    (hδp : δ ≤ ‖p₀‖) : ‖quadSeries p₀ a 2‖ ≤ 1 / δ ^ 2 := by
  rw [quadSeries_two, ContinuousMultilinearMap.uncurryRight_norm]
  rw [LinearIsometryEquiv.norm_map]
  refine norm_bilCoeff_le (hδ := hδ) ?_
  rw [ha]
  exact pow_le_pow_left₀ hδ.le hδp 2

end NormBounds

/-- The explicit uniform bound on the coefficients of `extSeries`. -/
lemma norm_extSeries_le_exp (p₀ : E) (a α : ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hα : ∀ n, |Ring.choose α n| ≤ C ^ n) :
    ∀ d, ‖extSeries p₀ a α d‖ ≤
      (2 * C * max 1 (max ‖quadSeries p₀ a 1‖ ‖quadSeries p₀ a 2‖)) ^ d := by
  set A : ℝ := max 1 (max ‖quadSeries p₀ a 1‖ ‖quadSeries p₀ a 2‖) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hq1 : ‖quadSeries p₀ a 1‖ ≤ A := le_trans (le_max_left _ _) (le_max_right 1 _)
  have hq2 : ‖quadSeries p₀ a 2‖ ≤ A := le_trans (le_max_right _ _) (le_max_right 1 _)
  have hA2 : A ≤ A ^ 2 := by
    calc A = A * 1 := by ring
      _ ≤ A * A := by gcongr
      _ = A ^ 2 := by ring
  have hq : ∀ j : ℕ, ‖quadSeries p₀ a j‖ ≤ A ^ j := by
    intro j
    rcases lt_or_ge j 3 with hj | hj
    · interval_cases j
      · rw [quadSeries_zero, norm_zero]; positivity
      · simpa using hq1
      · exact le_trans hq2 hA2
    · rw [quadSeries_large p₀ a hj, norm_zero]
      positivity
  intro d
  calc ‖extSeries p₀ a α d‖
      = ‖∑ c : Composition d, (binomialSeries ℝ α).compAlongComposition (quadSeries p₀ a) c‖ :=
        rfl
    _ ≤ ∑ c : Composition d, ‖(binomialSeries ℝ α).compAlongComposition (quadSeries p₀ a) c‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : Composition d, C ^ d * A ^ d := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine le_trans (FormalMultilinearSeries.compAlongComposition_norm _ _ c) ?_
        rw [norm_binomialSeries]
        have h1 : |Ring.choose α c.length| ≤ C ^ d :=
          le_trans (hα c.length) (pow_le_pow_right₀ hC c.length_le)
        have h2 : ∏ i, ‖quadSeries p₀ a (c.blocksFun i)‖ ≤ A ^ d := by
          refine le_trans (Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => hq _)) ?_
          rw [Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (Fintype.card (Composition d) : ℝ) * (C ^ d * A ^ d) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ (d - 1) * (C ^ d * A ^ d) := by
        rw [composition_card]; push_cast; ring
    _ ≤ (2 * C * A) ^ d := by
        have h2d : (2:ℝ) ^ (d - 1) ≤ 2 ^ d :=
          pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
        have hthis := mul_le_mul_of_nonneg_right h2d (by positivity : (0:ℝ) ≤ C ^ d * A ^ d)
        calc (2:ℝ) ^ (d - 1) * (C ^ d * A ^ d) ≤ 2 ^ d * (C ^ d * A ^ d) := hthis
          _ = (2 * C * A) ^ d := by rw [mul_pow, mul_pow]; ring

lemma mem_eball_of_lt_coe {v : E} {ρ : ℝ≥0} (hv : ‖v‖ < (ρ : ℝ)) :
    v ∈ eball (0 : E) (ρ : ℝ≥0∞) := by
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe,
    ← NNReal.coe_lt_coe, coe_nnnorm]
  exact hv

lemma lt_coe_of_mem_eball {v : E} {ρ : ℝ≥0} (hv : v ∈ eball (0 : E) (ρ : ℝ≥0∞)) :
    ‖v‖ < (ρ : ℝ) := by
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe,
    ← NNReal.coe_lt_coe, coe_nnnorm] at hv
  exact hv

lemma hasFPowerSeriesOnBall_extSeries (p₀ : E) (a α : ℝ) {ρ : ℝ≥0} (hρ : 0 < ρ) {D : ℝ}
    (hD1 : 1 ≤ D) (hbound : ∀ d, ‖extSeries p₀ a α d‖ ≤ D ^ d) (hρD : (ρ : ℝ) ≤ 1 / D)
    (han : ∀ v : E, ‖v‖ < (ρ : ℝ) → -1 < quadFun p₀ a v) :
    HasFPowerSeriesOnBall (fun v : E => (1 + quadFun p₀ a v) ^ α) (extSeries p₀ a α) 0
      (ρ : ℝ≥0∞) := by
  have hDpos : (0:ℝ) < D := lt_of_lt_of_le zero_lt_one hD1
  have hnn : (0:ℝ) ≤ 1 / D := div_nonneg zero_le_one hDpos.le
  set r : ℝ≥0 := ⟨(1 / D : ℝ), hnn⟩ with hr
  have hrR : (r : ℝ) = 1 / D := rfl
  have hrad : (r : ℝ≥0∞) ≤ (extSeries p₀ a α).radius :=
    le_radius_extSeries p₀ a α hD1 hbound hrR
  have hρr : ρ ≤ r := by
    have h1 : (ρ : ℝ) ≤ (r : ℝ) := by rw [hrR]; exact hρD
    exact_mod_cast h1
  have hradρ : (ρ : ℝ≥0∞) ≤ (extSeries p₀ a α).radius :=
    (ENNReal.coe_le_coe.mpr hρr).trans hrad
  have hpos_rad : 0 < (extSeries p₀ a α).radius := lt_of_lt_of_le (ENNReal.coe_pos.mpr hρ) hradρ
  have h2 : HasFPowerSeriesOnBall (extSeries p₀ a α).sum (extSeries p₀ a α) 0
      (extSeries p₀ a α).radius := FormalMultilinearSeries.hasFPowerSeriesOnBall _ hpos_rad
  have heq := extSeries_sum_eq p₀ a α hρ hD1 hbound hρD han
  refine ⟨hradρ, ENNReal.coe_pos.mpr hρ, fun {v} hv => ?_⟩
  have hv' : ‖v‖ < (ρ : ℝ) := lt_coe_of_mem_eball hv
  rw [zero_add, heq v hv']
  have hv_enn : (‖v‖₊ : ℝ≥0∞) < (ρ : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm]; exact hv'
  have hv_rad : v ∈ eball (0:E) (extSeries p₀ a α).radius := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact lt_of_lt_of_le hv_enn hradρ
  simpa using h2.hasSum hv_rad

section Main

variable {n : ℕ}

lemma inv_pow_norm_eq (hn : 0 < n) {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] {p v : E'} (hp : p ≠ 0) :
    (‖v + p‖ ^ n)⁻¹
      = (‖p‖ ^ 2) ^ (-(n:ℝ)/2) * (1 + quadFun p (‖p‖ ^ 2) v) ^ (-(n:ℝ)/2) := by
  have hnormp : (0:ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have ha : (0:ℝ) ≤ ‖p‖ ^ 2 := by positivity
  have hprod : ‖p‖ ^ 2 * (1 + quadFun p (‖p‖ ^ 2) v) = ‖v + p‖ ^ 2 := by
    have h1q : 1 + quadFun p (‖p‖ ^ 2) v
        = (‖p‖ ^ 2 + (2 * inner ℝ p v + ‖v‖ ^ 2)) / ‖p‖ ^ 2 := by
      rw [quadFun]; field_simp
    rw [h1q, mul_div_cancel₀ _ (by positivity : (‖p‖ ^ 2 : ℝ) ≠ 0),
      norm_add_sq_real v p, real_inner_comm v p]
    ring
  have hprod' : (0:ℝ) ≤ (1 + quadFun p (‖p‖ ^ 2) v) * ‖p‖ ^ 2 := by
    rw [mul_comm, hprod]; positivity
  have h1qnn : (0:ℝ) ≤ 1 + quadFun p (‖p‖ ^ 2) v :=
    nonneg_of_mul_nonneg_left hprod' (by positivity : (0:ℝ) < ‖p‖ ^ 2)
  have h1 : (‖v + p‖ ^ 2) ^ (-(n:ℝ)/2) = (‖v + p‖ ^ n)⁻¹ := by
    rw [show ‖v + p‖ ^ 2 = ‖v + p‖ ^ (2:ℝ) from (Real.rpow_natCast (‖v + p‖) 2).symm]
    rw [← Real.rpow_mul (norm_nonneg (v + p)) 2 (-(n:ℝ)/2),
      show (2:ℝ) * (-(n:ℝ)/2) = -(n:ℝ) by ring,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [← h1, ← hprod, Real.mul_rpow ha h1qnn]

end Main

section SphereIntegral


lemma contDiffAt_inv_pow_norm {n : ℕ} (hn : 0 < n) {z : euc n} (hz : z ≠ 0) (d : ℕ) :
    ContDiffAt ℝ d (fun z : euc n => (‖z‖ ^ n)⁻¹) z := by
  refine ContDiffAt.inv ?_ (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
  exact (ContDiffAt.norm (𝕜 := ℝ) contDiffAt_id hz).pow n

lemma norm_extSeries_le_uniform (p₀ : E) (a α : ℝ) {C A₀ : ℝ} (hC : 1 ≤ C) (hA₀ : 1 ≤ A₀)
    (hα : ∀ n, |Ring.choose α n| ≤ C ^ n)
    (h1 : ‖quadSeries p₀ a 1‖ ≤ A₀) (h2 : ‖quadSeries p₀ a 2‖ ≤ A₀) :
    ∀ d, ‖extSeries p₀ a α d‖ ≤ (2 * C * A₀) ^ d := by
  intro d
  refine le_trans (norm_extSeries_le_exp p₀ a α hC hα d) ?_
  have hA : max 1 (max ‖quadSeries p₀ a 1‖ ‖quadSeries p₀ a 2‖) ≤ A₀ :=
    max_le hA₀ (max_le h1 h2)
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hA (by positivity)) d

end SphereIntegral


section MainProof

/-- `iteratedFDeriv` is insensitive to writing the base point translation on the left. -/
lemma iteratedFDeriv_add_left_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (f : E → F) (d : ℕ) (a : E) :
    iteratedFDeriv 𝕜 d (fun z => f (a + z)) 0 = iteratedFDeriv 𝕜 d f a := by
  rw [iteratedFDeriv_comp_add_left, add_zero]

/-- `(‖p‖^2)^(-(n:ℝ)/2) = (‖p‖^n)⁻¹`. -/
lemma rpow_sq_neg_half_eq_inv_pow {n : ℕ} {p : euc n} :
    (‖p‖ ^ 2) ^ (-(n:ℝ)/2) = (‖p‖ ^ n)⁻¹ := by
  have h := norm_nonneg p
  rw [show ‖p‖ ^ 2 = ‖p‖ ^ (2:ℝ) from (Real.rpow_natCast ‖p‖ 2).symm,
    ← Real.rpow_mul h 2 (-(n:ℝ)/2), show (2:ℝ) * (-(n:ℝ)/2) = -(n:ℝ) by ring,
    Real.rpow_neg h, Real.rpow_natCast]

/-- The formal power series of `w ↦ (‖p + w‖^n)⁻¹`, written as a series in `p`. -/
noncomputable def harmSeries {n : ℕ} (p : euc n) : FormalMultilinearSeries ℝ (euc n) ℝ :=
  (‖p‖ ^ n)⁻¹ • extSeries p (‖p‖ ^ 2) (-(n:ℝ)/2)

/-- The Taylor series of `G` at `p`, as a formal multilinear series. -/
noncomputable def taySeries {n : ℕ} (G : euc n → ℝ) (p : euc n) :
    FormalMultilinearSeries ℝ (euc n) ℝ :=
  fun d => (d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d G p

/-- The power series at `0` of `w ↦ (‖p + w‖^n)⁻¹`. -/
lemma hasFPowerSeriesOnBall_inv_pow_norm {n : ℕ} (hn : 0 < n) {p : euc n} (hp : p ≠ 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) {D : ℝ} (hD1 : 1 ≤ D)
    (hbound : ∀ d, ‖extSeries p (‖p‖ ^ 2) (-(n:ℝ)/2) d‖ ≤ D ^ d) (hρD : (ρ:ℝ) ≤ 1 / D)
    (han : ∀ v : euc n, ‖v‖ < (ρ:ℝ) → -1 < quadFun p (‖p‖ ^ 2) v) :
    HasFPowerSeriesOnBall (fun w : euc n => (‖p + w‖ ^ n)⁻¹) (harmSeries p) 0 (ρ : ℝ≥0∞) := by
  have hbase := hasFPowerSeriesOnBall_extSeries p (‖p‖ ^ 2) (-(n:ℝ)/2) hρ hD1 hbound hρD han
  refine (hbase.const_smul (c := (‖p‖ ^ n)⁻¹)).congr ?_
  intro v _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← rpow_sq_neg_half_eq_inv_pow, ← inv_pow_norm_eq hn hp (p := p) (v := v), add_comm p v]

theorem analyticAt_sphere_integral {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {gf : sphere (0 : euc n) 1 → ℝ} (hgf : Continuous gf)
    {y₀ : euc n} (hy₀ : ‖y₀‖ < R) :
    AnalyticAt ℝ (fun y : euc n =>
      ∫ u : sphere (0 : euc n) 1,
        (‖y - R • (u : euc n)‖ ^ n)⁻¹ * gf u
      ∂(MeasureTheory.volume : Measure (euc n)).toSphere) y₀ := by
  haveI hfin : IsFiniteMeasure ((MeasureTheory.volume : Measure (euc n)).toSphere) :=
    inferInstance
  haveI hcpt : CompactSpace (sphere (0 : euc n) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : euc n) 1)
  set δ : ℝ := R - ‖y₀‖ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨C, hC1, hCα⟩ := Commons.Analysis.Analytic.ring_choose_bound (-(n:ℝ)/2)
  set A : ℝ := max 1 (max (2/δ) (1/δ^2)) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA2δ : 2/δ ≤ A := le_trans (le_max_left _ _) (le_max_right 1 _)
  have hA1δ : 1/δ^2 ≤ A := le_trans (le_max_right _ _) (le_max_right 1 _)
  set D : ℝ := 2 * C * A with hDdef
  have hD1 : 1 ≤ D := by rw [hDdef]; nlinarith [hC1, hA1]
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hρposR : (0:ℝ) < min (δ/8) (1/(2*D)) := lt_min (by linarith) (by positivity)
  set ρ : ℝ≥0 := ⟨min (δ/8) (1/(2*D)), hρposR.le⟩ with hρdef
  have hρR : (ρ:ℝ) = min (δ/8) (1/(2*D)) := rfl
  have hρ : 0 < ρ := by
    have hh : (0:ℝ) < (ρ:ℝ) := by rw [hρR]; exact hρposR
    exact_mod_cast hh
  have hρ_le : (ρ:ℝ) ≤ δ/8 := by rw [hρR]; exact min_le_left _ _
  have hρ_le2 : (ρ:ℝ) ≤ 1/(2*D) := by rw [hρR]; exact min_le_right _ _
  have hρD : (ρ:ℝ) ≤ 1/D := by
    refine le_trans hρ_le2 ?_
    rw [one_div, one_div, inv_le_inv₀ (by positivity) hDpos]
    linarith
  set K : ℝ := ((MeasureTheory.volume : Measure (euc n)).toSphere).real univ with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set M : ℝ := ‖(⟨gf, hgf⟩ : C(sphere (0 : euc n) 1, ℝ))‖ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hM : ∀ u : sphere (0 : euc n) 1, ‖gf u‖ ≤ M :=
    fun u => by
      rw [hMdef]
      exact ContinuousMap.norm_coe_le_norm (⟨gf, hgf⟩ : C(sphere (0 : euc n) 1, ℝ)) u
  set P : sphere (0 : euc n) 1 → euc n := fun u => y₀ - R • (u : euc n) with hPdef
  have hPnorm : ∀ u : sphere (0 : euc n) 1, δ ≤ ‖P u‖ := by
    intro u
    have hpow : ‖(u : euc n)‖ = 1 := by
      have h := u.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    have hRu : ‖R • (u : euc n)‖ = R := by
      rw [norm_smul, hpow, mul_one, Real.norm_eq_abs, abs_of_pos hR]
    have h1 : ‖R • (u : euc n)‖ ≤ ‖y₀‖ + ‖P u‖ := by
      calc ‖R • (u : euc n)‖ = ‖y₀ - P u‖ := by
            rw [hPdef]; simp only [sub_sub_cancel]
        _ ≤ ‖y₀‖ + ‖P u‖ := norm_sub_le _ _
    rw [hRu] at h1
    rw [hδdef]; linarith
  have hPne : ∀ u : sphere (0 : euc n) 1, P u ≠ 0 := by
    intro u hh
    have h1 := hPnorm u
    rw [hh, norm_zero] at h1
    linarith
  have hbound : ∀ (u : sphere (0 : euc n) 1) (d : ℕ),
      ‖extSeries (P u) (‖P u‖ ^ 2) (-(n:ℝ)/2) d‖ ≤ D ^ d := by
    intro u d
    have hδp := hPnorm u
    have hq1 : ‖quadSeries (P u) (‖P u‖^2) 1‖ ≤ A :=
      le_trans (norm_quadSeries_one_le (P u) rfl hδ hδp) hA2δ
    have hq2 : ‖quadSeries (P u) (‖P u‖^2) 2‖ ≤ A :=
      le_trans (norm_quadSeries_two_le (P u) rfl hδ hδp) hA1δ
    have h := norm_extSeries_le_uniform (P u) (‖P u‖^2) (-(n:ℝ)/2) hC1 hA1 hCα hq1 hq2 d
    rw [hDdef]
    exact h
  have han : ∀ (u : sphere (0 : euc n) 1) (v : euc n), ‖v‖ < (ρ:ℝ) →
      -1 < quadFun (P u) (‖P u‖ ^ 2) v := by
    intro u v hv
    have hδp := hPnorm u
    have hδpos : 0 < ‖P u‖ := lt_of_lt_of_le hδ hδp
    have hquad : -2 * (‖v‖ / ‖P u‖) ≤ quadFun (P u) (‖P u‖ ^ 2) v := by
      have habs := (abs_le.mp (abs_real_inner_le_norm (P u) v)).1
      have hq : quadFun (P u) (‖P u‖ ^ 2) v
          = (2 * inner ℝ (P u) v + ‖v‖ ^ 2) / ‖P u‖ ^ 2 := rfl
      rw [hq, show -2 * (‖v‖ / ‖P u‖) = (-2 * ‖v‖) / ‖P u‖ by ring]
      rw [div_le_iff₀ hδpos,
        show (2 * inner ℝ (P u) v + ‖v‖ ^ 2) / ‖P u‖ ^ 2 * ‖P u‖
            = (2 * inner ℝ (P u) v + ‖v‖ ^ 2) / ‖P u‖ by field_simp,
        le_div_iff₀ hδpos]
      nlinarith [habs, sq_nonneg ‖v‖, norm_nonneg (P u), norm_nonneg v, hδpos]
    have hb : (‖v‖ / ‖P u‖) ≤ 1/8 := by
      rw [div_le_iff₀ hδpos]
      linarith [hv.le, hρ_le, hδp]
    linarith [hquad, hb]
  set Gfun : euc n → ℝ := fun z => (‖z‖ ^ n)⁻¹ with hGdef
  have hS : ∀ u : sphere (0:euc n) 1, HasFPowerSeriesOnBall (fun w : euc n => Gfun (P u + w))
      (harmSeries (P u)) 0 (ρ : ℝ≥0∞) := by
    intro u
    have h := hasFPowerSeriesOnBall_inv_pow_norm hn (hPne u) hρ hD1 (hbound u) hρD (han u)
    simpa only [hGdef] using h
  have hpserdiag : ∀ (u : sphere (0:euc n) 1) (d : ℕ) (y : euc n),
      harmSeries (P u) d (fun _ => y) = taySeries Gfun (P u) d (fun _ => y) := by
    intro u d y
    have h' : iteratedFDeriv ℝ d Gfun (P u) (fun _ => y)
        = (d.factorial : ℝ) * harmSeries (P u) d (fun _ => y) := by
      have h := (hS u).iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin d => y)
      rw [iteratedFDeriv_add_left_zero (f := Gfun) d (P u)] at h
      have hsum : (∑ σ : Equiv.Perm (Fin d),
            harmSeries (P u) d (fun i => (fun _ : Fin d => y) (σ i)))
          = ∑ _σ : Equiv.Perm (Fin d), harmSeries (P u) d (fun _ => y) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rfl
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul] at h
      simpa using h
    rw [taySeries, smul_apply, smul_eq_mul, h',
      inv_mul_cancel_left₀ (by exact_mod_cast Nat.factorial_ne_zero d : (d.factorial : ℝ) ≠ 0)]
  have hpser_bound : ∀ (u : sphere (0:euc n) 1) (d : ℕ),
      ‖taySeries Gfun (P u) d‖ ≤ (δ^n)⁻¹ * D^d := by
    intro u d
    have hIter : ‖iteratedFDeriv ℝ d Gfun (P u)‖
        ≤ (d.factorial : ℝ) * ‖harmSeries (P u) d‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound
        (M := (d.factorial : ℝ) * ‖harmSeries (P u) d‖) (by positivity) (fun v => ?_)
      have h := (hS u).iteratedFDeriv_eq_sum_of_completeSpace v
      rw [iteratedFDeriv_add_left_zero (f := Gfun) d (P u)] at h
      rw [h]
      calc ‖∑ σ : Equiv.Perm (Fin d), harmSeries (P u) d (fun i => v (σ i))‖
          ≤ ∑ σ : Equiv.Perm (Fin d), ‖harmSeries (P u) d (fun i => v (σ i))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _σ : Equiv.Perm (Fin d), ‖harmSeries (P u) d‖ * ∏ i, ‖v i‖ := by
            refine Finset.sum_le_sum (fun σ _ => ?_)
            calc ‖harmSeries (P u) d (fun i => v (σ i))‖
                ≤ ‖harmSeries (P u) d‖ * ∏ i, ‖v (σ i)‖ :=
                  ContinuousMultilinearMap.le_opNorm _ _
              _ = ‖harmSeries (P u) d‖ * ∏ i, ‖v i‖ := by
                  rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
        _ = (d.factorial : ℝ) * ‖harmSeries (P u) d‖ * ∏ i, ‖v i‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
              nsmul_eq_mul]
            ring
    have hSh : ‖harmSeries (P u) d‖ ≤ (δ^n)⁻¹ * D^d := by
      show ‖(‖P u‖^n)⁻¹ • extSeries (P u) (‖P u‖^2) (-(n:ℝ)/2) d‖ ≤ (δ^n)⁻¹ * D^d
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (‖P u‖^n)⁻¹)]
      refine mul_le_mul ?_ (hbound u d) (norm_nonneg _) (by positivity)
      exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hδ (hPnorm u)) n) (pow_pos hδ n)).mpr
        (pow_le_pow_left₀ hδ.le (hPnorm u) n)
    rw [taySeries, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (d.factorial:ℝ)⁻¹)]
    calc (d.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ d Gfun (P u)‖
        ≤ (d.factorial : ℝ)⁻¹ * ((d.factorial : ℝ) * ‖harmSeries (P u) d‖) :=
          mul_le_mul_of_nonneg_left hIter (by positivity)
      _ = ‖harmSeries (P u) d‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero d), one_mul]
      _ ≤ (δ^n)⁻¹ * D^d := hSh
  have hpsercont : ∀ d : ℕ, Continuous (fun u : sphere (0:euc n) 1 => taySeries Gfun (P u) d) := by
    intro d
    have hiter : Continuous (fun u : sphere (0:euc n) 1 => iteratedFDeriv ℝ d Gfun (P u)) := by
      refine continuous_iff_continuousAt.mpr (fun u => ?_)
      have hc : ContinuousAt (fun z : euc n => iteratedFDeriv ℝ d Gfun z) (P u) :=
        ContDiffAt.continuousAt_iteratedFDeriv
          (by rw [hGdef]; exact contDiffAt_inv_pow_norm hn (hPne u) d) le_rfl
      have hPc : ContinuousAt (fun u : sphere (0:euc n) 1 => P u) u := by
        rw [hPdef]
        exact ((continuous_const : Continuous (fun _ : sphere (0:euc n) 1 => y₀)).sub
          ((continuous_const : Continuous (fun _ : sphere (0:euc n) 1 => R)).smul
            (continuous_subtype_val :
              Continuous (fun u : sphere (0:euc n) 1 => (u : euc n))))).continuousAt
      exact hc.comp hPc
    have h := hiter.const_smul ((d.factorial : ℝ)⁻¹)
    convert h using 1
    funext u
    simp only [Pi.smul_apply, taySeries]
  have hpsm : ∀ d : ℕ, Continuous
      (fun u : sphere (0:euc n) 1 => gf u • taySeries Gfun (P u) d) :=
    fun d => Continuous.smul (X := euc n [×d]→L[ℝ] ℝ) hgf (hpsercont d)
  let Q : FormalMultilinearSeries ℝ (euc n) ℝ := fun d =>
    ∫ u : sphere (0:euc n) 1, gf u • taySeries Gfun (P u) d
      ∂(MeasureTheory.volume : Measure (euc n)).toSphere
  have hQint : ∀ d : ℕ, Integrable
      (fun u : sphere (0:euc n) 1 => gf u • taySeries Gfun (P u) d)
      ((MeasureTheory.volume : Measure (euc n)).toSphere) := fun d =>
    (hpsm d).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨Q, (ρ : ℝ≥0∞), ?_, ENNReal.coe_pos.mpr hρ, ?_⟩
  · have hrpos : (0:ℝ) < 1/D := by positivity
    set r : ℝ≥0 := ⟨1/D, hrpos.le⟩ with hrdef
    have hrR : (r:ℝ) = 1/D := rfl
    have hrle : ρ ≤ r := by
      rw [← NNReal.coe_le_coe, hrR]; exact hρD
    refine (ENNReal.coe_le_coe.mpr hrle).trans ?_
    refine FormalMultilinearSeries.le_radius_of_bound Q (M * (δ^n)⁻¹ * K) (fun d => ?_)
    have hQd : ‖Q d‖ ≤ M * (δ^n)⁻¹ * D^d * K := by
      show ‖∫ u, gf u • taySeries Gfun (P u) d
        ∂(MeasureTheory.volume : Measure (euc n)).toSphere‖ ≤ M * (δ^n)⁻¹ * D^d * K
      refine le_trans (MeasureTheory.norm_integral_le_of_norm_le_const
        (C := M * (δ^n)⁻¹ * D^d) ?_) (le_of_eq ?_)
      · refine Filter.Eventually.of_forall (fun u => ?_)
        calc ‖gf u • taySeries Gfun (P u) d‖ ≤ ‖gf u‖ * ‖taySeries Gfun (P u) d‖ := by
              rw [norm_smul]
          _ ≤ M * ((δ^n)⁻¹ * D^d) :=
              mul_le_mul (hM u) (hpser_bound u d) (norm_nonneg _) hM0
          _ = M * (δ^n)⁻¹ * D^d := by ring
      · rw [← hKdef]
    have hDinv : D * (1/D) = 1 := by
      field_simp
    have hpD : (D:ℝ)^d * (1/D)^d ≤ 1 := by
      have h : (D:ℝ)^d * (1/D)^d = 1 := by
        calc (D:ℝ)^d * (1/D)^d = (D * (1/D))^d := (mul_pow D (1/D) d).symm
          _ = 1 := by rw [hDinv, one_pow]
      exact h.le
    have hfinal : (M * (δ^n)⁻¹ * D^d * K) * (1/D)^d ≤ M * (δ^n)⁻¹ * K := by
      calc (M * (δ^n)⁻¹ * D^d * K) * (1/D)^d
          = M * (δ^n)⁻¹ * K * ((D:ℝ)^d * (1/D)^d) := by ring
        _ ≤ M * (δ^n)⁻¹ * K * 1 := mul_le_mul_of_nonneg_left hpD (by positivity)
        _ = M * (δ^n)⁻¹ * K := by ring
    rw [hrR]
    exact le_trans (mul_le_mul_of_nonneg_right hQd (by positivity)) hfinal
  · intro y hy
    have hyR : ‖y‖ < (ρ:ℝ) := lt_coe_of_mem_eball hy
    have hFcont : ∀ d : ℕ, Continuous (fun u : sphere (0:euc n) 1 =>
        (gf u • taySeries Gfun (P u) d) (fun _ => y)) := fun d =>
      (continuous_eval_const (fun _ : Fin d => y)).comp (hpsm d)
    have hFint : ∀ d : ℕ, Integrable
        (fun u : sphere (0:euc n) 1 => (gf u • taySeries Gfun (P u) d) (fun _ => y))
        ((MeasureTheory.volume : Measure (euc n)).toSphere) := fun d =>
      (hFcont d).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hFsum : Summable (fun d : ℕ => ∫ u : sphere (0:euc n) 1,
        ‖(gf u • taySeries Gfun (P u) d) (fun _ => y)‖
        ∂(MeasureTheory.volume : Measure (euc n)).toSphere) := by
      have hgeom : Summable (fun d : ℕ => (D * ‖y‖) ^ d) := by
        refine summable_geometric_of_norm_lt_one ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hDpos.le (norm_nonneg y))]
        calc D * ‖y‖ ≤ D * (ρ:ℝ) := mul_le_mul_of_nonneg_left hyR.le hDpos.le
          _ ≤ D * (1/(2*D)) := mul_le_mul_of_nonneg_left hρ_le2 hDpos.le
          _ = (1:ℝ)/2 := by field_simp
          _ < 1 := by norm_num
      refine (hgeom.mul_left (M * (δ^n)⁻¹ * K)).of_nonneg_of_le
        (fun d => integral_nonneg (fun u => norm_nonneg _)) (fun d => ?_)
      have hpt : ∀ u : sphere (0:euc n) 1,
          ‖(gf u • taySeries Gfun (P u) d) (fun _ => y)‖
            ≤ M * (δ^n)⁻¹ * D^d * ‖y‖^d := by
        intro u
        have h1 : ‖(gf u • taySeries Gfun (P u) d) (fun _ => y)‖
            ≤ ‖gf u‖ * (‖taySeries Gfun (P u) d‖ * ‖y‖^d) := by
          rw [smul_apply, norm_smul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖(taySeries Gfun (P u) d) (fun _ => y)‖
              ≤ ‖taySeries Gfun (P u) d‖ * ∏ _i : Fin d, ‖y‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
            _ = ‖taySeries Gfun (P u) d‖ * ‖y‖^d := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        calc ‖(gf u • taySeries Gfun (P u) d) (fun _ => y)‖
            ≤ ‖gf u‖ * (‖taySeries Gfun (P u) d‖ * ‖y‖^d) := h1
          _ ≤ M * ((δ^n)⁻¹ * D^d * ‖y‖^d) := by
              refine mul_le_mul (hM u) ?_ (by positivity) hM0
              exact mul_le_mul_of_nonneg_right (hpser_bound u d) (by positivity)
          _ = M * (δ^n)⁻¹ * D^d * ‖y‖^d := by ring
      calc ∫ u, ‖(gf u • taySeries Gfun (P u) d) (fun _ => y)‖
            ∂(MeasureTheory.volume : Measure (euc n)).toSphere
          ≤ ∫ u, (M * (δ^n)⁻¹ * D^d * ‖y‖^d)
            ∂(MeasureTheory.volume : Measure (euc n)).toSphere :=
            integral_mono (hFint d).norm (integrable_const _) (fun u => hpt u)
        _ = (M * (δ^n)⁻¹ * D^d * ‖y‖^d) * K := by
            rw [integral_const, smul_eq_mul, ← hKdef, mul_comm]
        _ = (M * (δ^n)⁻¹ * K) * (D * ‖y‖)^d := by rw [mul_pow]; ring
    have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
    have hQd : ∀ d : ℕ, (∫ u, (gf u • taySeries Gfun (P u) d) (fun _ => y)
        ∂(MeasureTheory.volume : Measure (euc n)).toSphere) = Q d (fun _ => y) := by
      intro d
      rw [← ContinuousMultilinearMap.integral_apply (𝕜 := ℝ) (hQint d) (fun _ : Fin d => y)]
    rw [show (fun d : ℕ => ∫ u, (gf u • taySeries Gfun (P u) d) (fun _ => y)
        ∂(MeasureTheory.volume : Measure (euc n)).toSphere) = fun d => Q d (fun _ => y)
        from funext hQd] at hmain
    have hpt2 : (∫ u, ∑' d : ℕ, (gf u • taySeries Gfun (P u) d) (fun _ => y)
        ∂(MeasureTheory.volume : Measure (euc n)).toSphere)
        = ∫ u, Gfun (P u + y) * gf u
            ∂(MeasureTheory.volume : Measure (euc n)).toSphere := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show (∑' d : ℕ, (gf u • taySeries Gfun (P u) d) (fun _ => y))
        = Gfun (P u + y) * gf u
      have hSsum := (hS u).hasSum hy
      simp only [zero_add] at hSsum
      have hSsum2 : HasSum (fun d : ℕ => gf u * (harmSeries (P u) d (fun _ => y)))
          (gf u * Gfun (P u + y)) := HasSum.mul_left (gf u) hSsum
      have hterm : ∀ d : ℕ, (gf u • taySeries Gfun (P u) d) (fun _ => y)
          = gf u * (harmSeries (P u) d (fun _ => y)) := by
        intro d
        rw [smul_apply, smul_eq_mul, ← hpserdiag u d y]
      rw [tsum_congr hterm, hSsum2.tsum_eq, mul_comm]
    have h3 : (∫ u, Gfun (P u + y) * gf u
          ∂(MeasureTheory.volume : Measure (euc n)).toSphere)
        = ∫ u, (‖y₀ + y - R • (u : euc n)‖ ^ n)⁻¹ * gf u
            ∂(MeasureTheory.volume : Measure (euc n)).toSphere := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show Gfun (P u + y) * gf u = (‖y₀ + y - R • (u : euc n)‖ ^ n)⁻¹ * gf u
      simp only [hGdef]
      rw [show P u + y = y₀ + y - R • (u : euc n) by rw [hPdef]; module]
    rw [hpt2, h3] at hmain
    exact hmain

end MainProof

section Top

theorem contDiffOn_top_pExt {n : ℕ} (hn : 0 < n) {c : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hR : 0 < R) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g (Metric.sphere c R)) :
    ContDiffOn ℝ ⊤ (Commons.Analysis.Harmonic.pExt n c R g) (Metric.ball c R) := by
  have hmem : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      c + R • (u : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere c R := by
    intro u
    rw [Metric.mem_sphere, dist_eq_norm]
    have h1 : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      have h := u.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [add_sub_cancel_left, norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_pos hR]
  have hgf : Continuous (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      g (c + R • (u : EuclideanSpace ℝ (Fin n)))) :=
    hg.comp_continuous (by fun_prop) hmem
  refine AnalyticOn.contDiffOn ?_ Metric.isOpen_ball.uniqueDiffOn
  intro x hx
  have hy₀ : ‖x - c‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    exact hx
  have hG := analyticAt_sphere_integral hn hR hgf hy₀
  set Afac : ℝ := R^n / (sphereArea n * R^2) with hAfacdef
  have hlin : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => z - c) x := by
    have h := AnalyticAt.sub (𝕜 := ℝ)
      (f := (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)))
      (g := fun _ : EuclideanSpace ℝ (Fin n) => c)
      (analyticAt_id (z := x)) (analyticAt_const (x := x))
    exact AnalyticAt.congr h (Filter.Eventually.of_forall (fun z => rfl))
  have h2 : AnalyticAt ℝ ((fun y : EuclideanSpace ℝ (Fin n) =>
      ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (‖y - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹
        * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) ∘
      (fun z : EuclideanSpace ℝ (Fin n) => z - c)) x :=
    AnalyticAt.comp (f := fun z : EuclideanSpace ℝ (Fin n) => z - c) hG hlin
  have h3 : AnalyticAt ℝ ((fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) ∘
      (fun z : EuclideanSpace ℝ (Fin n) => z - c)) x :=
    AnalyticAt.comp (f := fun z : EuclideanSpace ℝ (Fin n) => z - c)
      (analyticAt_norm_sq (x - c)) hlin
  have h4 : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => R^2 - ‖z - c‖^2) x := by
    have h := AnalyticAt.sub (𝕜 := ℝ) (f := fun _ : EuclideanSpace ℝ (Fin n) => R^2)
      (analyticAt_const (x := x)) h3
    exact AnalyticAt.congr h (Filter.Eventually.of_forall (fun z => rfl))
  have h5 : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin n) =>
      Afac * ((R^2 - ‖z - c‖^2) *
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (‖z - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹
          * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) x :=
    AnalyticAt.const_smul (c := Afac) (AnalyticAt.mul (𝕜 := ℝ) (A := ℝ) h4 h2)
  have hfun : ∀ z : EuclideanSpace ℝ (Fin n), pExt n c R g z = Afac *
      ((R^2 - ‖z - c‖^2) * ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (‖z - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹
        * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
    intro z
    have h1 : (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          pKern n c R z u * g (c + R • (u : EuclideanSpace ℝ (Fin n))))
        = fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => Afac *
            ((R^2 - ‖z - c‖^2) * ((‖z - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹
              * g (c + R • (u : EuclideanSpace ℝ (Fin n))))) := by
      funext u
      rw [pKern, ← hAfacdef]
      ring
    rw [pExt, h1, integral_const_mul, integral_const_mul]
  exact (h5.congr (Filter.Eventually.of_forall (fun z => (hfun z).symm))).analyticWithinAt

end Top
