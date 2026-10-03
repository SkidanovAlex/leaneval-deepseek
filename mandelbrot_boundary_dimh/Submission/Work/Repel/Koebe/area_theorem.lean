import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Repel.Koebe.Setup
import Submission.Work.Repel.Koebe.taylor_coeff_expansion
import Submission.Work.Repel.Koebe.wind_eq_one
import Submission.Work.Repel.Koebe.wind_eq_zero_of_image
import Submission.Work.Repel.Koebe.wind_eq_zero_of_norm_lt
import Submission.Work.Repel.Koebe.volume_image_sphere_eq_zero
import Submission.Work.Repel.Koebe.dbar_wind_integral
import Submission.Work.Repel.Koebe.circleIntegral_conj_mul_deriv
import Submission.Work.Repel.Koebe.summable_mul_normSq_div

/-!
# Grönwall's area theorem, first-coefficient form

We prove: if `g` is holomorphic and injective on the exterior `{1 < ‖z‖}` of the unit disc with
`g(w) = w + b/w + …` at infinity, then `‖b‖ ≤ 1`.
-/

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Repel.Koebe

/-- Smooth cutoff, `1` on the closed ball of radius `M` and supported in the ball of radius `M+1`. -/
noncomputable def cutoff (M : ℝ) (ζ : ℂ) : ℝ := Real.smoothTransition (M ^ 2 + 1 - ‖ζ‖ ^ 2)

lemma cutoff_nonneg (M : ℝ) (ζ : ℂ) : 0 ≤ cutoff M ζ := Real.smoothTransition.nonneg _

lemma cutoff_le_one (M : ℝ) (ζ : ℂ) : cutoff M ζ ≤ 1 := Real.smoothTransition.le_one _

lemma cutoff_eq_one {M : ℝ} (hM : 0 ≤ M) {ζ : ℂ} (h : ‖ζ‖ ≤ M) : cutoff M ζ = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le]
  have h' : ‖ζ‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg ζ, h]
  linarith

lemma cutoff_eq_zero {M : ℝ} {ζ : ℂ} (h : |M| + 1 ≤ ‖ζ‖) : cutoff M ζ = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos]
  have h' : (|M| + 1) ^ 2 ≤ ‖ζ‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have h2 : (|M| + 1) ^ 2 = |M| ^ 2 + 2 * |M| + 1 := by ring
  have h3 : |M| ^ 2 = M ^ 2 := sq_abs M
  nlinarith [abs_nonneg M]

lemma contDiff_normSq : ContDiff ℝ 1 (fun ζ : ℂ => ‖ζ‖ ^ 2) := by
  have h : (fun ζ : ℂ => ‖ζ‖ ^ 2) = fun ζ : ℂ => ζ.re * ζ.re + ζ.im * ζ.im := by
    funext ζ; rw [Complex.sq_norm, Complex.normSq_apply]
  rw [h]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

lemma cutoff_contDiff (M : ℝ) : ContDiff ℝ 1 (cutoff M) := by
  have h2 : ContDiff ℝ 1 (fun ζ : ℂ => M ^ 2 + 1 - ‖ζ‖ ^ 2) :=
    contDiff_const.sub contDiff_normSq
  exact (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).comp h2

lemma cutoff_hasCompactSupport (M : ℝ) : HasCompactSupport (cutoff M) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℂ) (|M| + 1)) ?_
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  rw [not_le] at h
  refine hζ ?_
  exact cutoff_eq_zero (le_of_lt h)

/-- `∂̄ (star ζ) = 2`. -/
lemma dbar_star (z : ℂ) : Work.Analysis.Complex.DbarCauchy.dbar (fun ζ : ℂ => star ζ) z = 2 := by
  have hf : HasFDerivAt (fun ζ : ℂ => star ζ) ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    ContinuousLinearMap.hasFDerivAt ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)
  rw [Work.Analysis.Complex.DbarCauchy.dbar, hf.fderiv]
  norm_num [Complex.conj_I]

/-- The bounded region `V_r`: the complement of the image of the closed exterior of the circle. -/
def Vr (g : ℂ → ℂ) (r : ℝ) : Set ℂ := {ζ : ℂ | ∀ z : ℂ, r ≤ ‖z‖ → g z ≠ ζ}

lemma measurableSet_Vr {g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z) : MeasurableSet (Vr g r) := by
  have hset : Vr g r = (⋃ n : ℕ, g '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ (n : ℝ)})ᶜ := by
    ext ζ
    constructor
    · intro h hmem
      obtain ⟨n, hmem'⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨z, ⟨hz, _⟩, hval⟩ := hmem'
      exact h z hz hval
    · intro h z hz hval
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact h (Set.mem_iUnion.mpr ⟨n, ⟨z, ⟨hz, hn⟩, hval⟩⟩)
  rw [hset]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun n => ?_)
  have hcont : ContinuousOn g {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ (n : ℝ)} := fun z hz =>
    (hg z (lt_of_lt_of_le hr hz.1)).continuousAt.continuousWithinAt
  have hcomp : IsCompact {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ (n : ℝ)} := by
    have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ (n : ℝ)} ⊆ Metric.closedBall (0 : ℂ) n :=
      fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
    have hclosed : IsClosed {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ (n : ℝ)} :=
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    exact (isCompact_closedBall (0 : ℂ) n).of_isClosed_subset hclosed hsub
  exact (hcomp.image_of_continuousOn hcont).isClosed.measurableSet

lemma wind_eq_one_of_mem_Vr {g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2)
    {ζ : ℂ} (hζ : ζ ∈ Vr g r) : wind g r ζ = 1 :=
  wind_eq_one hr hg hbound (fun z hz => hζ z hz)

lemma wind_eq_zero_of_mem_compl {g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2)
    (hinj : Set.InjOn g {z : ℂ | 1 < ‖z‖})
    {ζ : ℂ} (hζ : ∃ z : ℂ, r < ‖z‖ ∧ g z = ζ) : wind g r ζ = 0 := by
  obtain ⟨z, hz, hzval⟩ := hζ
  exact wind_eq_zero_of_image hr hg hbound hinj hz hzval

/-- Off the curve `g '' {‖z‖ = r}`, the winding number is the indicator of `Vr`. -/
lemma wind_eq_indicator_ae {g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2)
    (hinj : Set.InjOn g {z : ℂ | 1 < ‖z‖}) :
    wind g r =ᵐ[volume] (Vr g r).indicator (fun _ => (1 : ℂ)) := by
  show ∀ᵐ x ∂volume, wind g r x = (Vr g r).indicator (fun _ => (1 : ℂ)) x
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (volume_image_sphere_eq_zero hr hg)
  intro ζ hζ
  simp only [Set.mem_setOf_eq] at hζ
  by_contra hnot
  have hoff : ∀ z : ℂ, ‖z‖ = r → g z ≠ ζ := by
    intro z hz hval
    exact hnot ⟨z, by simpa [Metric.mem_sphere, dist_eq_norm] using hz, hval⟩
  rcases em (ζ ∈ Vr g r) with hV | hV
  · rw [wind_eq_one_of_mem_Vr hr hg hbound hV, Set.indicator_of_mem hV] at hζ
    exact hζ rfl
  · have hVu : ¬ ∀ z : ℂ, r ≤ ‖z‖ → g z ≠ ζ := hV
    simp only [not_forall, not_imp, not_ne_iff] at hVu
    obtain ⟨z, hz, hval⟩ := hVu
    have hzlt : r < ‖z‖ := lt_of_le_of_ne hz fun h => hoff z h.symm hval
    rw [wind_eq_zero_of_mem_compl hr hg hbound hinj ⟨z, hzlt, hval⟩,
      Set.indicator_of_notMem hV] at hζ
    exact hζ rfl

theorem area_theorem {g : ℂ → ℂ} {b : ℂ}
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hinj : Set.InjOn g {z : ℂ | 1 < ‖z‖})
    (hlim : Filter.Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    ‖b‖ ≤ 1 := by
  classical
  obtain ⟨c, hc0, hc1, hcHas, hcSum⟩ :=
    taylor_coeff_expansion (analyticOnNhd_phi hg hlim) phi_zero
  have hc1b : c 1 = b := by rw [hc1]; exact deriv_phi_zero hlim
  obtain ⟨Rb, hRb1, hRb⟩ := exists_bound_sub_id hlim
  have hbnd : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2 := ⟨Rb, hRb⟩
  have hexp : ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun k : ℕ => c k / z ^ k) (g z - z) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz)
    have hlt : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hz
    have h1 : HasSum (fun k : ℕ => c k * (z⁻¹ : ℂ) ^ k) (phi g z⁻¹) :=
      hcHas z⁻¹ (inv_ne_zero hz0) hlt
    rw [show phi g z⁻¹ = g z - z from by rw [phi_apply (inv_ne_zero hz0), inv_inv]] at h1
    exact h1.congr_fun fun k => by rw [div_eq_mul_inv, inv_pow]
  have key : ∀ r : ℝ, 1 < r → (∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) ≤ r ^ 2 := by
    intro r hr
    have hcont : ContinuousOn g (Metric.sphere (0 : ℂ) r) := by
      intro z hz
      have hz' : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      exact (hg z (by rw [hz']; exact hr)).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hcont
    set M : ℝ := max 2 (B + 1) with hMdef
    have hM0 : 0 ≤ M := le_trans (by norm_num) (le_max_left _ _)
    have hBM : B < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hglt : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ < M := fun z hz =>
      lt_of_le_of_lt (hB z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)) hBM
    have hstar : ContDiff ℝ 1 (fun ζ : ℂ => star ζ) := Complex.conjCLE.contDiff
    have hchi : ContDiff ℝ 1 (fun ζ : ℂ => (cutoff M ζ : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (cutoff_contDiff M)
    have hG1 : ContDiff ℝ 1 (fun ζ : ℂ => star ζ * (cutoff M ζ : ℂ)) := hstar.mul hchi
    have hGc : HasCompactSupport (fun ζ : ℂ => star ζ * (cutoff M ζ : ℂ)) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_closedBall (0 : ℂ) (M + 1)) ?_
      intro ζ hζ
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      by_contra h
      rw [not_le] at h
      have hz : cutoff M ζ = 0 := cutoff_eq_zero (by rw [abs_of_nonneg hM0]; linarith)
      exact hζ (by simp [hz])
    have hid := dbar_wind_integral g r (fun ζ : ℂ => star ζ * (cutoff M ζ : ℂ)) hr hg hG1 hGc
    have hdbar : ∀ ζ : ℂ,
        Work.Analysis.Complex.DbarCauchy.dbar (fun ζ : ℂ => star ζ * (cutoff M ζ : ℂ)) ζ
        = 2 * (cutoff M ζ : ℂ)
          + star ζ * Work.Analysis.Complex.DbarCauchy.dbar (fun η : ℂ => (cutoff M η : ℂ)) ζ := by
      intro ζ
      rw [Work.Analysis.Complex.DbarCauchy.dbar_mul _ _ ζ
        (hstar.differentiable (by norm_num)).differentiableAt
        (hchi.differentiable (by norm_num)).differentiableAt, dbar_star]
    have hzero : ∀ ζ : ℂ, wind g r ζ * (star ζ *
        Work.Analysis.Complex.DbarCauchy.dbar (fun η : ℂ => (cutoff M η : ℂ)) ζ) = 0 := by
      intro ζ
      rcases lt_or_ge ‖ζ‖ M with h | h
      · -- inside: `χ` is locally `1` near `ζ`
        have hconst : (fun η : ℂ => (cutoff M η : ℂ)) =ᶠ[𝓝 ζ] fun _ => (1 : ℂ) := by
          filter_upwards [Metric.ball_mem_nhds ζ (by linarith : (0:ℝ) < M - ‖ζ‖)] with η hη
          have h1 : ‖η - ζ‖ < M - ‖ζ‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hη
          have h2 : ‖η‖ < M := by
            have h4 : ‖η‖ ≤ ‖ζ‖ + ‖η - ζ‖ := by
              have h5 : η = (η - ζ) + ζ := by ring
              calc ‖η‖ = ‖(η - ζ) + ζ‖ := congrArg norm h5
                _ ≤ ‖η - ζ‖ + ‖ζ‖ := norm_add_le _ _
                _ = ‖ζ‖ + ‖η - ζ‖ := by ring
            linarith
          rw [cutoff_eq_one hM0 h2.le]
          simp
        rw [Work.Analysis.Complex.DbarCauchy.dbar_congr hconst,
          Work.Analysis.Complex.DbarCauchy.dbar_const]
        ring
      · -- far out: `wind` vanishes
        rw [wind_eq_zero_of_norm_lt hr hg (fun z hz => lt_of_lt_of_le (hglt z hz) h)]
        ring
    have hident : 2 * (∫ ζ : ℂ, wind g r ζ * (cutoff M ζ : ℂ))
        = -Complex.I * circleIntegral (fun z : ℂ =>
            (star (g z)) * (cutoff M (g z) : ℂ) * deriv g z) 0 r := by
      rw [← hid, ← MeasureTheory.integral_const_mul]
      congr 1
      funext ζ
      rw [hdbar, mul_add, hzero]
      ring
    have hcirc := circleIntegral_conj_mul_deriv (g := g) (c := c) hr hexp
      (fun ρ hρ => hcSum ρ hρ)
    have hcirc' : circleIntegral (fun z : ℂ =>
        (star (g z)) * (cutoff M (g z) : ℂ) * deriv g z) 0 r
        = circleIntegral (fun z : ℂ => (star (g z)) * deriv g z) 0 r := by
      refine circleIntegral.integral_congr (by linarith : (0:ℝ) ≤ r) ?_
      intro z hz
      have hz' : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have h1 : cutoff M (g z) = 1 := cutoff_eq_one hM0 (le_of_lt (hglt z hz'))
      simp [h1]
    have hcongr : (∫ ζ : ℂ, wind g r ζ * (cutoff M ζ : ℂ))
        = ∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℂ)) ζ) * (cutoff M ζ : ℂ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [wind_eq_indicator_ae hr hg hbnd hinj] with ζ hζ
      rw [hζ]
    have hInt : Integrable (fun ζ : ℂ => ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ) := by
      refine MeasureTheory.Integrable.mono'
        (g := fun ζ : ℂ => (Metric.closedBall (0:ℂ) (M + 1)).indicator (fun _ => (1:ℝ)) ζ) ?_ ?_ ?_
      · exact (integrable_indicator_iff (isCompact_closedBall (0:ℂ) (M + 1)).measurableSet).mpr
          (integrableOn_const (isCompact_closedBall (0:ℂ) (M+1)).measure_lt_top.ne (by simp))
      · exact ((measurable_const.indicator (measurableSet_Vr hr hg)).mul
          (cutoff_contDiff M).continuous.measurable).aestronglyMeasurable
      · filter_upwards with ζ
        have h1 : |(Vr g r).indicator (fun _ => (1 : ℝ)) ζ| ≤ 1 := by
          by_cases h : ζ ∈ Vr g r
          · rw [Set.indicator_of_mem h]; norm_num
          · rw [Set.indicator_of_notMem h]; norm_num
        have h2 : cutoff M ζ ≤ 1 := cutoff_le_one M ζ
        have h3 : 0 ≤ cutoff M ζ := cutoff_nonneg M ζ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h3]
        have hstep : |(Vr g r).indicator (fun _ => (1 : ℝ)) ζ| * cutoff M ζ ≤ 1 := by
          calc |(Vr g r).indicator (fun _ => (1 : ℝ)) ζ| * cutoff M ζ
              ≤ 1 * 1 := mul_le_mul h1 h2 h3 (by norm_num)
            _ = 1 := by ring
        by_cases h : ζ ∈ Metric.closedBall (0:ℂ) (M+1)
        · rw [Set.indicator_of_mem h]
          exact hstep
        · have hout : M + 1 < ‖ζ‖ := by
            simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using h
          have hcz : cutoff M ζ = 0 := cutoff_eq_zero (by rw [abs_of_nonneg hM0]; linarith)
          simp [Set.indicator_of_notMem h, hcz]
    have hreal : 0 ≤ ∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ := by
      refine integral_nonneg fun ζ => ?_
      by_cases h : ζ ∈ Vr g r
      · have h1 : ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ = cutoff M ζ := by
          simp [Set.indicator_of_mem h]
        rw [h1]; exact cutoff_nonneg M ζ
      · have h1 : ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ = 0 := by
          simp [Set.indicator_of_notMem h]
        rw [h1]; exact le_refl 0
    have hcast : ∀ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℂ)) ζ) * (cutoff M ζ : ℂ)
        = ((↑(((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ) : ℝ) : ℂ) := by
      intro ζ
      by_cases h : ζ ∈ Vr g r
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul, one_mul]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, zero_mul]
        simp
    have hcompl : (∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℂ)) ζ) * (cutoff M ζ : ℂ))
        = ((∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ : ℝ) : ℂ) := by
      simp only [hcast]
      exact Complex.ofRealCLM.integral_comp_comm hInt
    have hident2 : 2 * (∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℂ)) ζ) * (cutoff M ζ : ℂ))
        = 2 * ((1 / (2 * Complex.I)) *
            circleIntegral (fun z : ℂ => (star (g z)) * deriv g z) 0 r) := by
      have h3 : (-Complex.I : ℂ) = 2 * (1 / (2 * Complex.I)) := by
        field_simp
        rw [Complex.I_sq]
        norm_num
      rw [← hcongr, hident, hcirc', h3, mul_assoc]
    have hident3 : 2 * ((1 / (2 * Complex.I)) *
          circleIntegral (fun z : ℂ => (star (g z)) * deriv g z) 0 r)
        = 2 * ((Real.pi : ℂ) * ((r : ℂ) ^ 2 -
            ↑(∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)))) := by
      rw [hcirc]
    have h2 : (∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℂ)) ζ) * (cutoff M ζ : ℂ))
        = (Real.pi : ℂ) * ((r : ℂ) ^ 2 -
            ↑(∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m))) :=
      mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) (hident2.trans hident3)
    have hkeyC : ((Real.pi * (r ^ 2 - ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) : ℝ) : ℂ)
        = (Real.pi : ℂ) * ((r : ℂ) ^ 2 -
            ↑(∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m))) := by
      push_cast
      ring
    have hkey : Real.pi * (r ^ 2 - ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m))
        = ∫ ζ : ℂ, ((Vr g r).indicator (fun _ => (1 : ℝ)) ζ) * cutoff M ζ := by
      apply Complex.ofReal_injective
      rw [hkeyC, ← h2, hcompl]
    have hfin : 0 ≤ Real.pi * (r ^ 2 - ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) := by
      rw [hkey]
      exact hreal
    have hfin' := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp hfin
    linarith
  have hstep : ∀ r : ℝ, 1 < r → ‖c 1‖ ^ 2 ≤ r ^ 4 := by
    intro r hr
    have h := key r hr
    have hnn : ∀ m : ℕ, 0 ≤ (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) := fun m => by positivity
    have hsum : Summable (fun m : ℕ => (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) :=
      summable_mul_normSq_div hcSum hr
    have h2 : (1 : ℝ) * ‖c 1‖ ^ 2 / r ^ (2 * 1)
        ≤ ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) := by
      have := Summable.sum_le_tsum {1} (fun i _ => hnn i) hsum
      simpa using this
    have h3 : ‖c 1‖ ^ 2 / r ^ 2
        ≤ ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) := by
      simpa using h2
    have h4 : ‖c 1‖ ^ 2 / r ^ 2 ≤ r ^ 2 := le_trans h3 h
    have hr2 : 0 < r ^ 2 := by positivity
    rw [div_le_iff₀ hr2] at h4
    calc ‖c 1‖ ^ 2 ≤ r ^ 2 * r ^ 2 := h4
      _ = r ^ 4 := by ring
  have hfinal : ‖c 1‖ ^ 2 ≤ 1 := by
    by_contra hc
    have hc' : 1 < ‖c 1‖ ^ 2 := not_le.mp hc
    have hpos : 0 < ‖c 1‖ ^ 2 - 1 := by linarith
    have hδ0 : 0 < min 1 ((‖c 1‖ ^ 2 - 1) / 32) :=
      lt_min (by norm_num) (by linarith)
    have hδ1 : min 1 ((‖c 1‖ ^ 2 - 1) / 32) ≤ 1 := min_le_left _ _
    have hδ2 : min 1 ((‖c 1‖ ^ 2 - 1) / 32) ≤ (‖c 1‖ ^ 2 - 1) / 32 := min_le_right _ _
    have h4 := hstep (1 + min 1 ((‖c 1‖ ^ 2 - 1) / 32)) (by linarith)
    have h5 : (1 + min 1 ((‖c 1‖ ^ 2 - 1) / 32)) ^ 4
        ≤ 1 + 16 * ((‖c 1‖ ^ 2 - 1) / 32) := by
      nlinarith [hδ0.le, hδ1, hδ2, sq_nonneg (min 1 ((‖c 1‖ ^ 2 - 1) / 32)),
        pow_nonneg hδ0.le 3, pow_nonneg hδ0.le 4]
    linarith
  have hb1 : ‖c 1‖ ≤ 1 :=
    le_trans (le_abs_self _) ((sq_le_one_iff_abs_le_one (a := ‖c 1‖)).mp hfinal)
  rw [← hc1b]
  exact hb1

end Work.Repel.Koebe
