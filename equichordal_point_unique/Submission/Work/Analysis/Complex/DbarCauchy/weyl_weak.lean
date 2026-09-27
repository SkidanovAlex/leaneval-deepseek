
import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar_zero
import Submission.Work.Analysis.Complex.DbarCauchy.mollify_weak
import Submission.Work.Analysis.Complex.Mollify.mollify_contDiff
import Submission.Work.Analysis.Complex.MeanValue.norm_sq_mul_le_integral_ball
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball

open MeasureTheory Set Filter Metric
open scoped Topology Convolution

/-!
# Weyl's lemma, weak form (PROVED)

A locally `L²` (indeed globally `L¹` and `L²`) function on an open `U ⊆ ℂ` whose `∂̄`-pairings
against all compactly supported `C¹` test functions supported in `U` vanish agrees a.e. with an
analytic function near every point of `U`.

This is the analytic prerequisite of the divisor chapter: it converts the `L²` weak solutions
produced by the Hörmander engine (`Work.Analysis.Complex.Hormander.exists_dbar_solution_weighted`)
into honest holomorphic functions.  The proof is the classical mollification argument:

1. `u n := u ⋆ ρ n` is smooth (`Mollify.mollify_contDiff`), has the same weak `∂̄`-equation on the
   `ε`-shrunk domain (`mollify_weak`), hence `∂̄ (u n) = 0` pointwise there (`dbar_eq_zero_of_weak`)
   and so `u n` is analytic there (the differentiable Weyl lemma `analyticOnNhd_of_dbar_eq_zero`);
2. the family `(u n)` is locally bounded, uniformly in `n`: the pointwise Cauchy–Schwarz bound
   `norm_mollify_sq_le_convolution` dominates `‖u n‖²` by the integrable `ρ n ⋆ ‖u‖²`, hence
   `∫ ‖u n‖² ≤ ∫ ‖u‖²` (`integral_norm_sq_mollify_le`), and the area mean value inequality
   (`MeanValue.norm_sq_mul_le_integral_ball`) turns that into a pointwise bound;
3. Montel (`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball`) gives a
   locally uniformly convergent subsequence with analytic limit `g₀`;
4. the mollifications converge a.e. to `u`
   (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), which identifies `g₀` with
   `u` a.e.

Main result: `Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar_zero_memLp`.
-/


noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- The mollifier family used in Weyl's lemma. -/
noncomputable def weylBump (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := r / (2 * (n + 1))
  rOut := r / (n + 1)
  rIn_pos := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_pos hr (by linarith)
  rIn_lt_rOut := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [div_lt_div_iff_of_pos_left hr]
    · linarith
    all_goals linarith

@[simp] theorem weylBump_rIn (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (weylBump r hr n).rIn = r / (2 * ((n : ℝ) + 1)) := rfl

@[simp] theorem weylBump_rOut (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (weylBump r hr n).rOut = r / ((n : ℝ) + 1) := rfl

theorem weylBump_rOut_tendsto (r : ℝ) :
    Tendsto (fun n : ℕ => r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact tendsto_const_nhds.div_atTop h1

/-- **Weyl's lemma, weak form (global `L²` version).** -/
theorem analyticOnNhd_of_weak_dbar_zero_memLp {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : Integrable u volume) (hu2 : MemLp u 2 volume)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z in U, u z * dbar φ z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ Metric.closedBall z₀ δ ⊆ U ∧
      AnalyticOnNhd ℂ g (Metric.ball z₀ δ) ∧
      ∀ᵐ z ∂(volume.restrict (Metric.ball z₀ δ)), u z = g z := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set δ : ℝ := R / 32 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδR : δ ≤ R / 2 := by rw [hδdef]; linarith
  have hclosed : Metric.closedBall z₀ δ ⊆ U := by
    intro z hz
    exact hRU (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  have hBmid : Metric.ball z₀ (R / 2) ⊆ U :=
    (Metric.ball_subset_ball (by linarith)).trans hRU
  -- the mollifiers
  have hr : (0 : ℝ) < δ := hδ
  let φ' : ℕ → ContDiffBump (0 : ℂ) := fun n => weylBump δ hr n
  let ρ : ℕ → ℂ → ℝ := fun n => (φ' n).normed volume
  let un : ℕ → ℂ → ℂ := fun n z => ∫ t, ρ n t • u (z - t)
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ' n).contDiff_normed (n := (1 : ℕ∞))
  have hρcd : ∀ n, Continuous (ρ n) := fun n => (hρc1 n).continuous
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n => (φ' n).hasCompactSupport_normed
  have hρint : ∀ n, ∫ t, ρ n t = 1 := fun n => (φ' n).integral_normed
  have hρnn : ∀ n t, 0 ≤ ρ n t := fun n t => (φ' n).nonneg_normed t
  have hρint_rho : ∀ n, Integrable (ρ n) volume := fun n => (φ' n).integrable_normed
  have hρbdd : ∀ n, ∃ c : ℝ, ∀ᵐ t ∂volume, ‖ρ n t‖ ≤ c := by
    intro n
    obtain ⟨C, hC⟩ := (hρcs n).isCompact.exists_bound_of_continuousOn (hρcd n).continuousOn
    refine ⟨max C 0, Filter.Eventually.of_forall fun t => ?_⟩
    by_cases ht : t ∈ tsupport (ρ n)
    · exact le_trans (hC t ht) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht, norm_zero]
      exact le_max_right _ _
  have hε : ∀ n t, t ∈ tsupport (ρ n) → ‖t‖ ≤ δ / ((n : ℝ) + 1) := by
    intro n t ht
    have h1 : (φ' n).rOut = δ / ((n : ℝ) + 1) := rfl
    rw [show ρ n = (φ' n).normed volume from rfl, ContDiffBump.tsupport_normed_eq, h1] at ht
    simpa [dist_eq_norm] using Metric.mem_closedBall.mp ht
  -- the weak equation on the big ball
  have hweak_big : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball z₀ R → ∫ z in Metric.ball z₀ R, u z * dbar φ z = 0 := by
    intro φ hφc hφs hφU
    have hzeroR : ∀ z : ℂ, z ∉ Metric.ball z₀ R → u z * dbar φ z = 0 := by
      intro z hz
      have h0 : dbar φ z = 0 := by
        rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp (fun hmem => hz (hφU hmem)))]
        exact dbar_zero z
      rw [h0, mul_zero]
    have hzeroU : ∀ z : ℂ, z ∉ U → u z * dbar φ z = 0 := by
      intro z hz
      have h0 : dbar φ z = 0 := by
        rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp
          (fun hmem => hz (hφU.trans hRU hmem)))]
        exact dbar_zero z
      rw [h0, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroR,
      ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroU]
    exact h φ hφc hφs (hφU.trans hRU)
  -- `un n` satisfies the weak equation on `Bmid`
  have hweak_mid : ∀ n, ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball z₀ (R / 2) →
      ∫ z in Metric.ball z₀ (R / 2), un n z * dbar ψ z = 0 := by
    intro n ψ hψc hψs hψU
    have hΨ : ∀ z ∈ tsupport ψ, Metric.closedBall z (δ / ((n : ℝ) + 1)) ⊆ Metric.ball z₀ R := by
      intro z hz w hw
      have h1 : dist z w ≤ δ / ((n : ℝ) + 1) := by
        simpa [dist_comm] using Metric.mem_closedBall.mp hw
      have h2 : dist z z₀ < R / 2 := Metric.mem_ball.mp (hψU hz)
      have h3 : δ / ((n : ℝ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]; nlinarith [hδ]
      rw [Metric.mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ = dist z w + dist z z₀ := by rw [dist_comm]
        _ < R := by linarith
    have h0 := mollify_weak (Metric.isOpen_ball) (hu.locallyIntegrable) hweak_big
      (hρc1 n) (hρcs n) (fun t ht => hε n t ht) ψ hψc hψs hΨ
    rw [show (∫ z in Metric.ball z₀ (R / 2), un n z * dbar ψ z)
        = ∫ z, un n z * dbar ψ z from
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (fun z hz => by
        have h0' : dbar ψ z = 0 := by
          rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp (fun hmem => hz (hψU hmem)))]
          exact dbar_zero z
        rw [h0', mul_zero])]
    exact h0
  -- analyticity of `un n` on `Bmid`
  have hun_cd : ∀ n, ContDiff ℝ 1 (un n) := fun n =>
    Work.Analysis.Complex.Mollify.mollify_contDiff (hu.locallyIntegrable) (hρc1 n) (hρcs n)
  have hAn : ∀ n, AnalyticOnNhd ℂ (un n) (Metric.ball z₀ (R / 2)) := by
    intro n
    have hcd : ContDiff ℝ 1 (un n) := hun_cd n
    have h0 : ∀ z ∈ Metric.ball z₀ (R / 2), dbar (un n) z = 0 :=
      dbar_eq_zero_of_weak Metric.isOpen_ball hcd (hweak_mid n)
    exact analyticOnNhd_of_dbar_eq_zero Metric.isOpen_ball
      (fun z hz => (hcd.differentiable (by norm_num)).differentiableAt) h0
  -- the uniform bound
  have hM : 0 ≤ ∫ z, ‖u z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
  have hbound : ∀ n z, z ∈ Metric.ball z₀ δ → ‖un n z‖ ^ 2 ≤ (∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2) := by
    intro n z hz
    have hsubC : Metric.closedBall z δ ⊆ Metric.ball z₀ (R / 2) := by
      intro w hw
      rw [Metric.mem_ball]
      have h1 : dist w z ≤ δ := by simpa [dist_comm] using Metric.mem_closedBall.mp hw
      have h2 : dist z z₀ < δ := Metric.mem_ball.mp hz
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < δ + δ := by linarith
        _ = R / 16 := by rw [hδdef]; ring
        _ < R / 2 := by linarith
    have hsub : Metric.ball z δ ⊆ Metric.ball z₀ (R / 2) :=
      Metric.ball_subset_closedBall.trans hsubC
    have hd : DiffContOnCl ℂ (un n) (Metric.ball z δ) :=
      ⟨(hAn n).mono hsub |>.differentiableOn, (hAn n).continuousOn.mono fun w hw => by
        rw [closure_ball z (ne_of_gt hδ)] at hw
        exact hsubC hw⟩
    have hmv := Work.Analysis.Complex.MeanValue.norm_sq_mul_le_integral_ball
      (u := un n) (c := z) (ρ := δ) hδ hd
    have hcont : ContinuousOn (fun w : ℂ => ‖un n w‖ ^ 2) (Metric.closedBall z δ) := by
      change ContinuousOn ((fun w : ℂ => ‖un n w‖) ^ 2) (Metric.closedBall z δ)
      exact (ContinuousOn.norm ((hAn n).continuousOn.mono fun w hw => hsubC hw)).pow 2
    have hF2 : Integrable (fun w : ℂ => ‖u w‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).mp hu2
    have hgint : Integrable (fun w : ℂ =>
        (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w : ℂ => ‖u w‖ ^ 2)) w) volume :=
      (hρint_rho n).integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (f := ρ n) (g := fun w : ℂ => ‖u w‖ ^ 2) hF2
    have hcc : Continuous (fun w : ℂ => ‖un n w‖ ^ 2) := by
      change Continuous ((fun w : ℂ => ‖un n w‖) ^ 2)
      exact (hun_cd n).continuous.norm.pow 2
    have hun2 : Integrable (fun w : ℂ => ‖un n w‖ ^ 2) volume := by
      refine Integrable.mono' (f := fun w : ℂ => ‖un n w‖ ^ 2) hgint
        hcc.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact norm_mollify_sq_le_convolution (hρnn n) (hρint_rho n) (hρbdd n) (hρint n) hu hu2 w
    have h1 : ∫ w in Metric.ball z δ, ‖un n w‖ ^ 2 ≤ ∫ w, ‖un n w‖ ^ 2 :=
      MeasureTheory.setIntegral_le_integral hun2
        (Filter.Eventually.of_forall fun w => sq_nonneg _)
    have h2 : ∫ w, ‖un n w‖ ^ 2 ≤ ∫ w, ‖u w‖ ^ 2 :=
      integral_norm_sq_mollify_le (hρnn n) (hρcd n) (hρcs n) (hρint n) hu hu2
    have h3 : ‖un n z‖ ^ 2 * (Real.pi * δ ^ 2) ≤ ∫ w, ‖u w‖ ^ 2 := hmv.trans (h1.trans h2)
    rw [div_eq_mul_inv, le_mul_inv_iff₀ (by positivity : (0:ℝ) < Real.pi * δ ^ 2)]
    linarith [h3]
  -- step 4: Montel on the scaled family
  set c : ℝ := Real.sqrt ((∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2)) + 1 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hsqrt1 : Real.sqrt ((∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2)) ≤ c := by
    rw [hcdef]; linarith [Real.sqrt_nonneg ((∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2))]
  have hsub' : Metric.ball z₀ δ ⊆ Metric.ball z₀ (R / 2) :=
    Metric.ball_subset_ball (by linarith [hδdef])
  set f : ℕ → ℂ → ℂ := fun n z => ((c⁻¹ : ℝ) : ℂ) * un n z with hfdef
  have han : ∀ n, AnalyticOnNhd ℂ (f n) (Metric.ball z₀ δ) := fun n =>
    (analyticOnNhd_const (v := ((c⁻¹ : ℝ) : ℂ))).mul ((hAn n).mono hsub')
  have hmon : ∀ n z, z ∈ Metric.ball z₀ δ → ‖f n z‖ ≤ 1 := by
    intro n z hz
    have h1 : ‖un n z‖ ^ 2 ≤ (∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2) := hbound n z hz
    have h2 : ‖un n z‖ ≤ Real.sqrt ((∫ w, ‖u w‖ ^ 2) / (Real.pi * δ ^ 2)) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt h1
    have h3 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
    have h4 : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hcpos)
    have h5 : ‖f n z‖ = c⁻¹ * ‖un n z‖ := by
      rw [hfdef]
      simp only []
      rw [← Complex.real_smul, norm_smul, Real.norm_of_nonneg h3]
    rw [h5, ← h4]
    exact mul_le_mul_of_nonneg_left (by linarith [h2, hsqrt1]) h3
  obtain ⟨φsub, g₀, hφmono, hconv, hg₀an⟩ :=
    Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball
      (c := z₀) (R := δ) hδ (f := f) (fun n z hz => (han n) z hz) hmon
  -- step 5: the mollifications converge a.e. to `u`
  have hae0 : ∀ᵐ z ∂volume, Tendsto (fun n : ℕ => un n z) atTop (𝓝 (u z)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
      (φ := φ') (l := atTop) (K := 2) (g := u)
      (by
        change Tendsto (fun n : ℕ => (weylBump δ hr n).rOut) atTop (𝓝 0)
        simpa only [weylBump_rOut] using weylBump_rOut_tendsto δ)
      (Filter.Eventually.of_forall fun n => by
        change (weylBump δ hr n).rOut ≤ 2 * (weylBump δ hr n).rIn
        simp only [weylBump_rOut, weylBump_rIn]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ((n : ℝ) + 1))]
        have h0 : (0:ℝ) < (n:ℝ) + 1 := by positivity
        field_simp
        linarith)
      hu.locallyIntegrable
    refine h.mono fun z hz => ?_
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply] using hz
  refine ⟨fun z => ((c : ℝ) : ℂ) * g₀ z, δ, hδ, hclosed,
    (analyticOnNhd_const (v := ((c : ℝ) : ℂ))).mul hg₀an, ?_⟩
  refine (MeasureTheory.ae_restrict_iff' (p := fun z : ℂ => u z = ((c : ℝ) : ℂ) * g₀ z)
    (s := Metric.ball z₀ δ) Metric.isOpen_ball.measurableSet).mpr ?_
  refine hae0.mono fun z hz hzball => ?_
  have hz2 : Tendsto (fun n : ℕ => f (φsub n) z) atTop (𝓝 (g₀ z)) := hconv.tendsto_at hzball
  have hz3 : Tendsto (fun n : ℕ => f (φsub n) z) atTop (𝓝 (((c⁻¹ : ℝ) : ℂ) * u z)) := by
    have h1 : Tendsto (fun n : ℕ => un (φsub n) z) atTop (𝓝 (u z)) :=
      hz.comp hφmono.tendsto_atTop
    have h2 := h1.const_mul (((c⁻¹ : ℝ) : ℂ))
    simpa only [hfdef] using h2
  have huniq : g₀ z = ((c⁻¹ : ℝ) : ℂ) * u z := tendsto_nhds_unique hz2 hz3
  have hcu : ((c : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hcpos), Complex.ofReal_one]
  calc u z = (((c : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ)) * u z := by rw [hcu, one_mul]
    _ = ((c : ℝ) : ℂ) * (((c⁻¹ : ℝ) : ℂ) * u z) := by ring
    _ = ((c : ℝ) : ℂ) * g₀ z := by rw [← huniq]

/-- **Weyl's lemma, weak form, local statement** (the reviewed form, with local integrability
hypotheses only).  A locally `L²` function on an open `U` whose `∂̄`-pairings against all test
functions supported in `U` vanish agrees a.e. with an analytic function on a neighbourhood of each
point of `U`.  Derived from `analyticOnNhd_of_weak_dbar_zero_memLp` by cutting `u` off with a ball:
the cutoff has compact support, hence is globally `L¹` and `L²`, and the weak equation transports
because `∂̄` of a test function vanishes off its (compact) support. -/
theorem analyticOnNhd_of_weak_dbar_zero {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : LocallyIntegrable u volume)
    (hu2 : LocallyIntegrable (fun z => ‖u z‖ ^ 2) volume)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z in U, u z * dbar φ z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ Metric.closedBall z₀ δ ⊆ U ∧
      AnalyticOnNhd ℂ g (Metric.ball z₀ δ) ∧
      ∀ᵐ z ∂(volume.restrict (Metric.ball z₀ δ)), u z = g z := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set ũ : ℂ → ℂ := (Metric.ball z₀ R).indicator u with hũ
  have hint : Integrable ũ volume :=
    (MeasureTheory.integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      ((hu.integrableOn_isCompact (isCompact_closedBall z₀ R)).mono_set
        Metric.ball_subset_closedBall)
  have hint2 : Integrable (fun z : ℂ => ‖ũ z‖ ^ 2) volume := by
    have h1 : Integrable ((Metric.ball z₀ R).indicator (fun z : ℂ => ‖u z‖ ^ 2)) volume :=
      (MeasureTheory.integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
        ((hu2.integrableOn_isCompact (isCompact_closedBall z₀ R)).mono_set
          Metric.ball_subset_closedBall)
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    change (Metric.ball z₀ R).indicator (fun z : ℂ => ‖u z‖ ^ 2) z = ‖ũ z‖ ^ 2
    rw [hũ]
    by_cases hz : z ∈ Metric.ball z₀ R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero, zero_pow (by norm_num)]
  have hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball z₀ R → ∫ z in Metric.ball z₀ R, ũ z * dbar φ z = 0 := by
    intro φ hφc hφs hφR
    have hzeroR : ∀ z : ℂ, z ∉ Metric.ball z₀ R → ũ z * dbar φ z = 0 := by
      intro z hz
      rw [hũ, Set.indicator_of_notMem hz, zero_mul]
    have hzeroU : ∀ z : ℂ, z ∉ U → u z * dbar φ z = 0 := by
      intro z hz
      have h0 : dbar φ z = 0 := by
        rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp
          (fun hmem => hz (hRU (hφR hmem))))]
        exact dbar_zero z
      rw [h0, mul_zero]
    have hEq : ∫ z : ℂ, ũ z * dbar φ z = ∫ z : ℂ, u z * dbar φ z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change ũ z * dbar φ z = u z * dbar φ z
      by_cases hz : z ∈ Metric.ball z₀ R
      · rw [hũ, Set.indicator_of_mem hz]
      · have h0 : dbar φ z = 0 := by
          rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp (fun hmem => hz (hφR hmem)))]
          exact dbar_zero z
        rw [hũ, Set.indicator_of_notMem hz, h0, mul_zero, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroR,
      hEq, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroU]
    exact h φ hφc hφs (hφR.trans hRU)
  obtain ⟨g, δ, hδ, hcl, hgan, hae⟩ :=
    analyticOnNhd_of_weak_dbar_zero_memLp Metric.isOpen_ball hint
      ((memLp_two_iff_integrable_sq_norm hint.1).mpr hint2) hweak (Metric.mem_ball_self hR)
  refine ⟨g, δ, hδ, hcl.trans hRU, hgan, ?_⟩
  refine (MeasureTheory.ae_restrict_iff' (p := fun z : ℂ => u z = g z)
    (s := Metric.ball z₀ δ) Metric.isOpen_ball.measurableSet).mpr ?_
  have h2 := (MeasureTheory.ae_restrict_iff' (p := fun z : ℂ => ũ z = g z)
    (s := Metric.ball z₀ δ) Metric.isOpen_ball.measurableSet).mp hae
  refine h2.mono fun z hz hzball => ?_
  have h3 : ũ z = u z := by
    rw [hũ, Set.indicator_of_mem
      (Metric.ball_subset_closedBall.trans hcl hzball)]
  rw [← h3]
  exact hz hzball

end Work.Analysis.Complex.DbarCauchy
