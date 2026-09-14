import Mathlib
import Submission.Commons.Analysis.Convex.exp_neg_integrable_of_convex_coercive
import Submission.Commons.Analysis.Convex.integral_Ioi_exp_neg_le
import Submission.Commons.Analysis.Convex.integral_Iic_exp_neg_le
import Submission.Commons.Analysis.Convex.exists_deriv_lower_bound_of_convexOn
import Submission.Commons.Analysis.Convex.exists_deriv_upper_bound_of_convexOn
import Submission.Commons.Analysis.Convex.integrableOn_deriv2_exp_neg_div_sq
import Submission.Commons.Analysis.Convex.integrableOn_deriv2_exp_neg_div_sq_Ici
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_Ioi_of_integrable
import Submission.Commons.Analysis.Integral.sq_integral_mul_le_integral_sq_mul

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- A fixed smooth bump: `1` on `[-1,1]` and supported in `(-2,2)`. -/
def cutoffB : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The cutoff function, as a plain function `ℝ → ℝ`. -/
def cutoff : ℝ → ℝ := cutoffB

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := cutoffB.nonneg
lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := cutoffB.le_one
lemma cutoff_contDiff : ContDiff ℝ 2 cutoff := cutoffB.contDiff
lemma cutoff_continuous : Continuous cutoff := cutoffB.continuous
lemma cutoff_hasCompactSupport : HasCompactSupport cutoff := cutoffB.hasCompactSupport

lemma cutoff_abs_le_one (x : ℝ) : |cutoff x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg x)]; exact cutoff_le_one x

lemma cutoff_zero {y : ℝ} (hy : 2 ≤ |y|) : cutoff y = 0 := by
  refine cutoffB.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]
  exact hy

lemma cutoff_one {y : ℝ} (hy : |y| ≤ 1) : cutoff y = 1 := by
  refine cutoffB.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hy

lemma cutoff_deriv_continuous : Continuous (deriv cutoff) :=
  cutoff_contDiff.continuous_deriv (by norm_num)

/-- The derivative of a compactly supported smooth bump is bounded. -/
lemma exists_bound_deriv_cutoff : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |deriv cutoff y| ≤ B := by
  obtain ⟨C, hC⟩ := cutoff_hasCompactSupport.deriv.isCompact.exists_bound_of_continuousOn
    cutoff_deriv_continuous.continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport (deriv cutoff)
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC y hy) (le_max_right _ _)
  · have h0 : deriv cutoff y = 0 :=
      (notMem_tsupport_iff_eventuallyEq (f := deriv cutoff) (x := y)).mp hy |>.eq_of_nhds
    rw [h0, abs_zero]
    exact le_max_left _ _


lemma cutoff_differentiable : Differentiable ℝ cutoff := cutoff_contDiff.differentiable (by norm_num)

lemma deriv_cutoff_div (M x : ℝ) :
    deriv (fun y : ℝ => cutoff (y / M)) x = deriv cutoff (x / M) * (1 / M) := by
  have h1 : HasDerivAt (fun y : ℝ => y / M) (1 / M) x := (hasDerivAt_id x).div_const M
  have h3 := (cutoff_differentiable (x / M)).hasDerivAt.comp x h1
  simpa [Function.comp_def] using h3.deriv

lemma deriv_cutoff_div_mul (u : ℝ → ℝ) (hu : Differentiable ℝ u) (M x : ℝ) :
    deriv (fun y : ℝ => cutoff (y / M) * u y) x
      = (deriv cutoff (x / M) * (1 / M)) * u x + cutoff (x / M) * deriv u x := by
  rw [show (fun y : ℝ => cutoff (y / M) * u y) = (fun y : ℝ => cutoff (y / M)) * u from rfl,
    deriv_mul]
  · rw [deriv_cutoff_div]
  · exact DifferentiableAt.comp x (cutoff_differentiable (x / M)) (differentiableAt_id.div_const M)
  · exact hu.differentiableAt

lemma abs_deriv_cutoff_div_mul_le (u : ℝ → ℝ) (hu : Differentiable ℝ u) (B : ℝ)
    (hB : ∀ y, |deriv cutoff y| ≤ B) {M : ℝ} (hM : 1 ≤ M) (x : ℝ) :
    |deriv (fun y : ℝ => cutoff (y / M) * u y) x| ≤ B * |u x| + |deriv u x| := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  rw [deriv_cutoff_div_mul u hu M x]
  have h2 : |deriv cutoff (x / M) * (1 / M)| ≤ B := by
    rw [abs_mul]
    have h3 : |1 / M| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]; linarith
    calc |deriv cutoff (x / M)| * |1 / M| ≤ B * 1 :=
          mul_le_mul (hB _) h3 (abs_nonneg _) hB0
      _ = B := mul_one B
  have h4 : |cutoff (x / M)| ≤ 1 := cutoff_abs_le_one _
  calc |(deriv cutoff (x / M) * (1 / M)) * u x + cutoff (x / M) * deriv u x|
      ≤ |(deriv cutoff (x / M) * (1 / M)) * u x| + |cutoff (x / M) * deriv u x| :=
        abs_add_le _ _
    _ = |deriv cutoff (x / M) * (1 / M)| * |u x| + |cutoff (x / M)| * |deriv u x| := by
        simp only [abs_mul]
    _ ≤ B * |u x| + 1 * |deriv u x| := by
        have h5 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (u x))
        have h6 := mul_le_mul_of_nonneg_right h4 (abs_nonneg (deriv u x))
        linarith
    _ = B * |u x| + |deriv u x| := by ring

lemma sq_deriv_cutoff_div_mul_le (u : ℝ → ℝ) (hu : Differentiable ℝ u) (B : ℝ)
    (hB : ∀ y, |deriv cutoff y| ≤ B) {M : ℝ} (hM : 1 ≤ M) (x : ℝ) :
    (deriv (fun y : ℝ => cutoff (y / M) * u y) x) ^ 2
      ≤ 2 * (deriv u x) ^ 2 + 2 * B ^ 2 * (u x) ^ 2 := by
  have h := abs_deriv_cutoff_div_mul_le u hu B hB hM x
  have hsq : (deriv (fun y : ℝ => cutoff (y / M) * u y) x) ^ 2
      ≤ (B * |u x| + |deriv u x|) ^ 2 := by
    rw [← sq_abs (deriv (fun y : ℝ => cutoff (y / M) * u y) x)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [hsq, sq_abs (u x), sq_abs (deriv u x), abs_nonneg (u x), sq_nonneg B,
    sq_nonneg (B * |u x| - |deriv u x|)]


/-- **Sharp Brascamp–Lieb in dimension one: reduction to compact support.**
If the sharp inequality holds for all `C¹` compactly supported test functions, then it holds for
all `C¹` test functions satisfying the stated integrability hypotheses. -/
theorem sharp_general_of_compactSupport
    (hcompact : ∀ (V u : ℝ → ℝ), ContDiff ℝ 2 V → ConvexOn ℝ Set.univ V →
      (∀ x, 0 < deriv (deriv V) x) → Filter.Tendsto V Filter.atTop Filter.atTop →
      Filter.Tendsto V Filter.atBot Filter.atTop → ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ x, u x ^ 2 * Real.exp (-(V x))) - (∫ x, u x * Real.exp (-(V x))) ^ 2 /
        (∫ x, Real.exp (-(V x))) ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))
    (V u : ℝ → ℝ)
    (hV : ContDiff ℝ 2 V) (hVconv : ConvexOn ℝ Set.univ V)
    (hV2 : ∀ x, 0 < deriv (deriv V) x)
    (hVtop : Filter.Tendsto V Filter.atTop Filter.atTop)
    (hVbot : Filter.Tendsto V Filter.atBot Filter.atTop)
    (hu : ContDiff ℝ 1 u)
    (hu1 : Integrable fun x => u x * Real.exp (-(V x)))
    (hu2 : Integrable fun x => u x ^ 2 * Real.exp (-(V x)))
    (huw : Integrable fun x => u x ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))
    (hud : Integrable fun x => (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x))) :
    (∫ x, u x ^ 2 * Real.exp (-(V x)))
        - (∫ x, u x * Real.exp (-(V x))) ^ 2 / (∫ x, Real.exp (-(V x)))
      ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_cutoff
  have hVcont : Continuous V := hV.continuous
  have hEcont : Continuous (fun x : ℝ => Real.exp (-(V x))) :=
    Real.continuous_exp.comp hVcont.neg
  have hucont : Continuous u := hu.continuous
  have hZ : Integrable (fun x => Real.exp (-(V x))) :=
    exp_neg_integrable_of_convex_coercive V hVconv hVtop hVbot
  have hZpos : 0 < ∫ x, Real.exp (-(V x)) := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hZ]
    have : Function.support (fun x : ℝ => Real.exp (-(V x))) = Set.univ := by
      ext x; simp [Function.mem_support]
    rw [this]; simp
  have habs : Integrable (fun x => |u x| * Real.exp (-(V x))) := by
    refine Integrable.mono' ((hu2.add hZ).const_mul (1 / 2)) ?_ ?_
    · exact (hucont.abs.mul hEcont).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_abs]
      have h1 : 2 * |u x| ≤ u x ^ 2 + 1 := by
        nlinarith [sq_nonneg (|u x| - 1), sq_abs (u x), abs_nonneg (u x)]
      calc |u x| * Real.exp (-(V x)) ≤ ((u x ^ 2 + 1) / 2) * Real.exp (-(V x)) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = (1 / 2) * (u x ^ 2 * Real.exp (-(V x)) + Real.exp (-(V x))) := by ring
  have hcut (M : ℝ) : ContDiff ℝ 1 (fun x : ℝ => cutoff (x / M)) :=
    (cutoff_contDiff.comp (contDiff_id.div_const M)).of_le (by norm_num)
  have hmul (M : ℝ) : ContDiff ℝ 1 (fun x : ℝ => cutoff (x / M) * u x) :=
    (hcut M).mul hu
  have hsupp : ∀ M : ℝ, 1 ≤ M → HasCompactSupport (fun x : ℝ => cutoff (x / M) * u x) := by
    intro M hM
    have hcs : HasCompactSupport (fun x : ℝ => cutoff (x / M)) := by
      refine HasCompactSupport.intro (K := Set.Icc (-(2 * M)) (2 * M)) isCompact_Icc ?_
      intro x hx
      have hx' : x < -(2 * M) ∨ 2 * M < x := by
        have h1 : ¬ (-(2 * M) ≤ x ∧ x ≤ 2 * M) := by
          simpa [Set.mem_Icc] using hx
        rcases not_and_or.mp h1 with h | h
        · exact Or.inl (not_le.mp h)
        · exact Or.inr (not_le.mp h)
      have hxabs : 2 * M < |x| := by
        rcases hx' with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hgt : 2 < |x / M| := by
        rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < M), lt_div_iff₀ (by linarith)]
        linarith
      exact cutoff_zero hgt.le
    exact hcs.mul_right
  -- Limit of the second moment
  have hlimA : Filter.Tendsto (fun M : ℝ => ∫ x, (cutoff (x / M) * u x) ^ 2 * Real.exp (-(V x)))
      Filter.atTop (𝓝 (∫ x, u x ^ 2 * Real.exp (-(V x)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => u x ^ 2 * Real.exp (-(V x))) ?_ ?_ hu2 ?_
    · filter_upwards with M
      exact ((((hcut M).continuous).mul hucont).pow 2 |>.mul hEcont).aestronglyMeasurable
    · filter_upwards with M
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hc2 : (cutoff (x / M)) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) (cutoff_abs_le_one _)
      calc (cutoff (x / M) * u x) ^ 2 * Real.exp (-(V x))
          = (cutoff (x / M)) ^ 2 * (u x ^ 2 * Real.exp (-(V x))) := by ring
        _ ≤ 1 * (u x ^ 2 * Real.exp (-(V x))) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = u x ^ 2 * Real.exp (-(V x)) := by ring
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hlim : Filter.Tendsto (fun M : ℝ => cutoff (x / M)) Filter.atTop (𝓝 1) := by
        have h1 : Filter.Tendsto (fun M : ℝ => x / M) Filter.atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (cutoff_continuous.tendsto 0).comp h1
        rwa [cutoff_one (y := 0) (by norm_num)] at h2
      have h3 : Filter.Tendsto (fun M : ℝ => (cutoff (x / M) * u x) ^ 2 * Real.exp (-(V x)))
          Filter.atTop (𝓝 (u x ^ 2 * Real.exp (-(V x)))) := by
        have h := (hlim.mul (tendsto_const_nhds (x := u x))).pow 2 |>.mul
          (tendsto_const_nhds (x := Real.exp (-(V x))))
        simpa using h
      exact h3
  -- Limit of the first moment
  have hlimB : Filter.Tendsto (fun M : ℝ => ∫ x, (cutoff (x / M) * u x) * Real.exp (-(V x)))
      Filter.atTop (𝓝 (∫ x, u x * Real.exp (-(V x)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => |u x| * Real.exp (-(V x))) ?_ ?_ habs ?_
    · filter_upwards with M
      exact ((((hcut M).continuous).mul hucont).mul hEcont).aestronglyMeasurable
    · filter_upwards with M
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      have h4 : |cutoff (x / M)| ≤ 1 := cutoff_abs_le_one _
      calc |cutoff (x / M)| * |u x| * Real.exp (-(V x))
          ≤ 1 * |u x| * Real.exp (-(V x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (abs_nonneg _))
              (Real.exp_pos _).le
        _ = |u x| * Real.exp (-(V x)) := by ring
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hlim : Filter.Tendsto (fun M : ℝ => cutoff (x / M)) Filter.atTop (𝓝 1) := by
        have h1 : Filter.Tendsto (fun M : ℝ => x / M) Filter.atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (cutoff_continuous.tendsto 0).comp h1
        rwa [cutoff_one (y := 0) (by norm_num)] at h2
      have h3 : Filter.Tendsto (fun M : ℝ => (cutoff (x / M) * u x) * Real.exp (-(V x)))
          Filter.atTop (𝓝 (u x * Real.exp (-(V x)))) := by
        have h := (hlim.mul (tendsto_const_nhds (x := u x))).mul
          (tendsto_const_nhds (x := Real.exp (-(V x))))
        simpa using h
      exact h3
  -- Limit of the Dirichlet term
  have hV''cont : Continuous (deriv (deriv V)) :=
    (hV.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hlimR : Filter.Tendsto
      (fun M : ℝ => ∫ x, (deriv (fun y : ℝ => cutoff (y / M) * u y) x) ^ 2 /
        deriv (deriv V) x * Real.exp (-(V x)))
      Filter.atTop (𝓝 (∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => 2 * ((deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))
        + (2 * B ^ 2) * (u x ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))) ?_ ?_ ?_ ?_
    · filter_upwards with M
      have hd : Continuous (deriv (fun y : ℝ => cutoff (y / M) * u y)) :=
        (hmul M).continuous_deriv (by norm_num)
      exact (((hd.pow 2).div hV''cont (fun x => ne_of_gt (hV2 x))).mul hEcont).aestronglyMeasurable
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with M hM
      filter_upwards with x
      have hV2x : 0 < deriv (deriv V) x := hV2 x
      have hbx := sq_deriv_cutoff_div_mul_le u (hu.differentiable (by norm_num)) B hB hM x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (deriv (fun y : ℝ => cutoff (y / M) * u y) x) ^ 2 / deriv (deriv V) x
            * Real.exp (-(V x))
          ≤ (2 * (deriv u x) ^ 2 + 2 * B ^ 2 * (u x) ^ 2) / deriv (deriv V) x
            * Real.exp (-(V x)) := by
            exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbx hV2x.le)
              (Real.exp_pos _).le
        _ = 2 * ((deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))
            + (2 * B ^ 2) * (u x ^ 2 / deriv (deriv V) x * Real.exp (-(V x))) := by
            ring
    · exact (hud.const_mul 2).add (huw.const_mul (2 * B ^ 2))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hV2x : deriv (deriv V) x ≠ 0 := ne_of_gt (hV2 x)
      have hlim : Filter.Tendsto (fun M : ℝ => cutoff (x / M)) Filter.atTop (𝓝 1) := by
        have h1 : Filter.Tendsto (fun M : ℝ => x / M) Filter.atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (cutoff_continuous.tendsto 0).comp h1
        rwa [cutoff_one (y := 0) (by norm_num)] at h2
      have hlim' : Filter.Tendsto (fun M : ℝ => deriv cutoff (x / M) * (1 / M))
          Filter.atTop (𝓝 0) := by
        have h1 : Filter.Tendsto (fun M : ℝ => x / M) Filter.atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (cutoff_deriv_continuous.tendsto 0).comp h1
        have h3 : Filter.Tendsto (fun M : ℝ => (1 : ℝ) / M) Filter.atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h4 := h2.mul h3
        have h5 : deriv cutoff 0 * (0 : ℝ) = 0 := by ring
        rw [h5] at h4
        exact h4
      have hder : Filter.Tendsto (fun M : ℝ => deriv (fun y : ℝ => cutoff (y / M) * u y) x)
          Filter.atTop (𝓝 (deriv u x)) := by
        have h := (hlim'.mul (tendsto_const_nhds (x := u x))).add
          (hlim.mul (tendsto_const_nhds (x := deriv u x)))
        have h6 : (0 : ℝ) * u x + 1 * deriv u x = deriv u x := by ring
        rw [h6] at h
        simpa [deriv_cutoff_div_mul u (hu.differentiable (by norm_num))] using h
      have hfin := ((hder.pow 2).div_const (deriv (deriv V) x)).mul
        (tendsto_const_nhds (x := Real.exp (-(V x))))
      simpa using hfin
  -- pass to the limit
  have hL : Filter.Tendsto
      (fun M : ℝ => (∫ x, (cutoff (x / M) * u x) ^ 2 * Real.exp (-(V x)))
        - (∫ x, (cutoff (x / M) * u x) * Real.exp (-(V x))) ^ 2 /
          (∫ x, Real.exp (-(V x))))
      Filter.atTop
      (𝓝 ((∫ x, u x ^ 2 * Real.exp (-(V x)))
        - (∫ x, u x * Real.exp (-(V x))) ^ 2 / (∫ x, Real.exp (-(V x))))) := by
    have h := hlimA.sub ((hlimB.pow 2).div_const (∫ x, Real.exp (-(V x))))
    simpa using h
  have hev : ∀ᶠ M in Filter.atTop,
      (∫ x, (cutoff (x / M) * u x) ^ 2 * Real.exp (-(V x)))
        - (∫ x, (cutoff (x / M) * u x) * Real.exp (-(V x))) ^ 2 / (∫ x, Real.exp (-(V x)))
      ≤ ∫ x, (deriv (fun y : ℝ => cutoff (y / M) * u y) x) ^ 2 / deriv (deriv V) x
          * Real.exp (-(V x)) :=
    (Filter.eventually_ge_atTop (1 : ℝ)).mono (fun M hM =>
      hcompact V (fun x => cutoff (x / M) * u x) hV hVconv hV2 hVtop hVbot (hmul M) (hsupp M hM))
  exact le_of_tendsto_of_tendsto hL hlimR hev



open MeasureTheory Set Filter
open scoped Real Topology


private lemma exists_bound_of_continuous_hasCompactSupport (f : ℝ → ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := hcs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

private lemma integral_Iic_eq (f : ℝ → ℝ) (hf : Integrable f) (x : ℝ) :
    (∫ s in Set.Iic x, f s) = (∫ s, f s) - (∫ s in Set.Ioi x, f s) := by
  have h := integral_add_compl (μ := volume) (s := Set.Ioi x) measurableSet_Ioi hf
  rw [Set.compl_Ioi] at h
  linarith

private lemma hasDerivAt_integral_Iic (f : ℝ → ℝ) (hf : Continuous f) (hint : Integrable f) (x : ℝ) :
    HasDerivAt (fun y => ∫ s in Set.Iic y, f s) (f x) x := by
  rw [show (fun y => ∫ s in Set.Iic y, f s)
      = fun y => (∫ s, f s) - ∫ s in Set.Ioi y, f s from funext (integral_Iic_eq f hint)]
  have hioi : HasDerivAt (fun y => ∫ s in Set.Ioi y, f s) (-(f x)) x :=
    Commons.Analysis.Calculus.hasDerivAt_integral_Ioi_of_integrable f hf hint x
  have := (hioi.neg).const_add (∫ s, f s)
  simpa [sub_eq_add_neg] using this

private lemma integral_Iic_nonneg_of_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ ∫ s in Set.Iic x, f s :=
  setIntegral_nonneg measurableSet_Iic (fun s _ => hf s)

private lemma integral_Ioi_nonneg_of_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ ∫ s in Set.Ioi x, f s :=
  setIntegral_nonneg measurableSet_Ioi (fun s _ => hf s)

private lemma arithA (a b c : ℝ) : -(a * -(b * c)) = b * a * c := by ring
private lemma arithC {a b : ℝ} (ha : a ≠ 0) : a * (b * (1 / a)) = b := by
  field_simp
private lemma arithD (e v r w : ℝ) : -(e * v * r + w) = v * (-(e * r)) - w := by ring

private lemma integral_sum_sub {f g h : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hh : Integrable h) :
    ∫ x, f x + g x - h x = ((∫ x, f x) + ∫ x, g x) - ∫ x, h x := by
  have h1 : ∫ x, f x + g x - h x = ∫ x, ((f + g) - h) x :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => rfl))
  rw [h1, MeasureTheory.integral_sub' (hf.add hg) hh, MeasureTheory.integral_add' hf hg]

private lemma integral_sub_add {f g h : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hh : Integrable h) :
    ∫ x, (f x - g x) + h x = ((∫ x, f x) - ∫ x, g x) + ∫ x, h x := by
  have h1 : ∫ x, (f x - g x) + h x = ∫ x, ((f - g) + h) x :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => rfl))
  rw [h1, MeasureTheory.integral_add' (hf.sub hg) hh, MeasureTheory.integral_sub' hf hg]

/-- Sharp Brascamp–Lieb in one dimension for compactly supported `C¹` test functions. -/
theorem sharp_compact_aux (V u : ℝ → ℝ) (hV : ContDiff ℝ 2 V) (hVconv : ConvexOn ℝ Set.univ V)
    (hV2 : ∀ x, 0 < deriv (deriv V) x)
    (hVtop : Filter.Tendsto V Filter.atTop Filter.atTop)
    (hVbot : Filter.Tendsto V Filter.atBot Filter.atTop)
    (hu : ContDiff ℝ 1 u) (huK : HasCompactSupport u) :
    (∫ x, u x ^ 2 * Real.exp (-(V x)))
        - (∫ x, u x * Real.exp (-(V x))) ^ 2 / (∫ x, Real.exp (-(V x)))
      ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)) := by
  have hVd : ∀ x, DifferentiableAt ℝ V x := fun x => hV.differentiable (by norm_num) x
  have hV1d : ∀ x, DifferentiableAt ℝ (deriv V) x := fun x =>
    (hV.deriv' (n := 1)).differentiable (by norm_num) x
  have hV1c : Continuous (deriv V) := (hV.deriv' (n := 1)).continuous
  have hV2c : Continuous (deriv (deriv V)) :=
    (hV.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hVcont : Continuous V := hV.continuous
  have hucont : Continuous u := hu.continuous
  have hducont : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  set ρ : ℝ → ℝ := fun x => Real.exp (-(V x)) with hρdef
  have hρcont : Continuous ρ := by rw [hρdef]; exact Real.continuous_exp.comp hVcont.neg
  have hρint : Integrable ρ := by
    rw [hρdef]
    exact Commons.Analysis.Convex.exp_neg_integrable_of_convex_coercive V hVconv hVtop hVbot
  have hρnonneg : ∀ x, 0 ≤ ρ x := fun x => (Real.exp_pos _).le
  have hρpos : ∀ x, 0 < ρ x := fun x => Real.exp_pos _
  have hZpos : 0 < ∫ x, ρ x := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall hρnonneg) hρint]
    have hs : Function.support ρ = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hρpos x)
    rw [hs]; simp
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_continuous_hasCompactSupport u hucont huK
  have huρ_int : Integrable (fun x => u x * ρ x) := by
    refine Integrable.mono' (hρint.const_mul B) ?_ ?_
    · exact (hucont.mul hρcont).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg x)]
      exact mul_le_mul_of_nonneg_right (hB x) (hρnonneg x)
  have hu2ρ_int : Integrable (fun x => u x ^ 2 * ρ x) := by
    refine Integrable.mono' (hρint.const_mul (B ^ 2)) ?_ ?_
    · exact ((hucont.pow 2).mul hρcont).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (hρnonneg x)
      nlinarith [hB x, abs_nonneg (u x), sq_abs (u x), sq_nonneg (u x)]
  have hducs : HasCompactSupport (deriv u) := huK.deriv
  have hqcont : Continuous (fun x => (deriv u x) ^ 2 / deriv (deriv V) x) :=
    (hducont.pow 2).div hV2c (fun x => ne_of_gt (hV2 x))
  have hqcs : HasCompactSupport (fun x => (deriv u x) ^ 2 / deriv (deriv V) x) := by
    refine hducs.mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hdu
    exact hx (by rw [hdu]; simp)
  obtain ⟨B'', hB''0, hB''⟩ := exists_bound_of_continuous_hasCompactSupport _ hqcont hqcs
  have hud_int : Integrable (fun x => (deriv u x) ^ 2 / deriv (deriv V) x * ρ x) := by
    refine Integrable.mono' (hρint.const_mul B'') ?_ ?_
    · exact (hqcont.mul hρcont).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg x)]
      exact mul_le_mul_of_nonneg_right (hB'' x) (hρnonneg x)
  set Z : ℝ := ∫ x, ρ x with hZdef
  have hZne : Z ≠ 0 := ne_of_gt (by rw [hZdef]; exact hZpos)
  set m : ℝ := (∫ x, u x * ρ x) / Z with hmdef
  have hmZ : m * (∫ x, ρ x) = ∫ x, u x * ρ x := by
    rw [hmdef, ← hZdef]; field_simp
  set w : ℝ → ℝ := fun x => u x - m with hwdef
  have hwderiv : ∀ x, deriv w x = deriv u x := by
    intro x
    rw [hwdef]
    exact (((hu.differentiable (by norm_num) x).hasDerivAt).sub_const m).deriv
  have hwcont : Continuous w := hucont.sub continuous_const
  have hwρ_int : Integrable (fun x => w x * ρ x) := by
    have h1 : (fun x => w x * ρ x) = fun x => u x * ρ x - m * ρ x := by
      funext x; rw [hwdef]; ring
    rw [h1]
    exact huρ_int.sub (hρint.const_mul m)
  have hwmean : ∫ x, w x * ρ x = 0 := by
    have h1 : (fun x => w x * ρ x) = fun x => u x * ρ x - m * ρ x := by
      funext x; rw [hwdef]; ring
    rw [h1, MeasureTheory.integral_sub huρ_int (hρint.const_mul m),
      MeasureTheory.integral_const_mul, hmZ, sub_self]
  have hw2ρ_int : Integrable (fun x => w x ^ 2 * ρ x) := by
    have hle : ∀ x, w x ^ 2 * ρ x ≤ (2 * u x ^ 2 + 2 * m ^ 2) * ρ x := by
      intro x
      rw [hwdef]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u x + m)]) (hρnonneg x)
    have hint : Integrable (fun x => (2 * u x ^ 2 + 2 * m ^ 2) * ρ x) := by
      have h2 : (fun x => (2 * u x ^ 2 + 2 * m ^ 2) * ρ x)
          = fun x => 2 * (u x ^ 2 * ρ x) + (2 * m ^ 2) * ρ x := by funext x; ring
      rw [h2]
      exact (hu2ρ_int.const_mul 2).add (hρint.const_mul (2 * m ^ 2))
    refine Integrable.mono' hint (hwcont.pow 2 |>.mul hρcont).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle x
  have hvar : ∫ x, w x ^ 2 * ρ x
      = (∫ x, u x ^ 2 * ρ x) - (∫ x, u x * ρ x) ^ 2 / Z := by
    have hexp : (fun x => w x ^ 2 * ρ x) =ᵐ[volume]
        fun x => u x ^ 2 * ρ x - (2 * m) * (u x * ρ x) + (m ^ 2) * ρ x := by
      filter_upwards with x
      rw [hwdef]; ring
    rw [integral_congr_ae hexp]
    have h1 : Integrable fun x => u x ^ 2 * ρ x - 2 * m * (u x * ρ x) :=
      hu2ρ_int.sub (huρ_int.const_mul (2 * m))
    have h2 : Integrable fun x => m ^ 2 * ρ x := hρint.const_mul (m ^ 2)
    have hfun : (fun x => u x ^ 2 * ρ x - 2 * m * (u x * ρ x) + m ^ 2 * ρ x)
        = fun x => (u x ^ 2 * ρ x - 2 * m * (u x * ρ x)) + m ^ 2 * ρ x := rfl
    rw [hfun, MeasureTheory.integral_add h1 h2]
    have h3 : Integrable fun x => 2 * m * (u x * ρ x) := huρ_int.const_mul (2 * m)
    rw [MeasureTheory.integral_sub hu2ρ_int h3, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rw [← hmZ, ← hZdef]
    field_simp
    ring
  suffices hgoal : ∫ x, w x ^ 2 * ρ x ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * ρ x by
    rw [hvar] at hgoal
    simpa only [hZdef] using hgoal
  obtain ⟨x₁, c₁, hc₁, hx₁⟩ :=
    Commons.Analysis.Convex.exists_deriv_lower_bound_of_convexOn V hVconv hVd hVtop
  obtain ⟨x₂, c₂, hc₂, hx₂⟩ :=
    Commons.Analysis.Convex.exists_deriv_upper_bound_of_convexOn V hVconv hVd hVbot
  obtain ⟨a₀, ha₀⟩ := huK.isCompact.bddBelow
  obtain ⟨b₀, hb₀⟩ := huK.isCompact.bddAbove
  set a : ℝ := min (a₀ - 1) (min x₂ 0) with hadef
  set b : ℝ := max (b₀ + 1) (max x₁ 1) with hbdef
  have haa₀ : a ≤ a₀ - 1 := min_le_left _ _
  have hax₂ : a ≤ x₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have ha0 : a ≤ 0 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hbb₀ : b₀ + 1 ≤ b := le_max_left _ _
  have hbx₁ : x₁ ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) (le_max_right _ _)
  have hab : a ≤ b := by linarith
  have hu_le : ∀ x, x ≤ a → u x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport u := subset_tsupport u ((Function.mem_support (f := u)).mpr hne)
    have ha0x : a₀ ≤ x := ha₀ hmem
    linarith [haa₀, hx, ha0x]
  have hu_ge : ∀ x, b ≤ x → u x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport u := subset_tsupport u ((Function.mem_support (f := u)).mpr hne)
    have hb0x : x ≤ b₀ := hb₀ hmem
    linarith [hbb₀, hx, hb0x]
  have hV'neg : ∀ x, x ≤ a → deriv V x ≤ -c₂ := fun x hx => hx₂ x (le_trans hx hax₂)
  have hV'pos : ∀ x, b ≤ x → c₁ ≤ deriv V x := fun x hx => hx₁ x (le_trans hbx₁ hx)
  have hexpV : ∀ x, Real.exp (V x) * ρ x = 1 := by
    intro x; rw [hρdef, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  set p : ℝ → ℝ := fun x => -(Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s) with hpdef
  have hpcont : Continuous p := by
    rw [hpdef]
    exact (Real.continuous_exp.comp hVcont).mul
      (continuous_iff_continuousAt.mpr (fun x =>
        (hasDerivAt_integral_Iic _ (hwcont.mul hρcont) hwρ_int x).continuousAt)) |>.neg
  have hp_has : ∀ x, HasDerivAt p (deriv V x * p x - w x) x := by
    intro x
    have hR : HasDerivAt (fun y => ∫ s in Set.Iic y, w s * ρ s) (w x * ρ x) x :=
      hasDerivAt_integral_Iic _ (hwcont.mul hρcont) hwρ_int x
    have he : HasDerivAt (fun y => Real.exp (V y)) (Real.exp (V x) * deriv V x) x :=
      (hVd x).hasDerivAt.exp
    have hkey : Real.exp (V x) * (w x * ρ x) = w x := by
      rw [show Real.exp (V x) * (w x * ρ x) = w x * (Real.exp (V x) * ρ x) by ring,
        hexpV x, mul_one]
    have hmul : HasDerivAt (fun y : ℝ => Real.exp (V y) * ∫ s in Set.Iic y, w s * ρ s)
        (deriv V x * (Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s) + w x) x := by
      have h := he.mul hR
      rw [hkey] at h
      exact h.congr_deriv (by ring)
    have h3 : HasDerivAt (fun y : ℝ => -(Real.exp (V y) * ∫ s in Set.Iic y, w s * ρ s))
        (-(deriv V x * (Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s) + w x)) x :=
      (hmul.neg).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => rfl))
    have hval : -(deriv V x * (Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s) + w x)
        = deriv V x * (-(Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s)) - w x := by ring
    rw [hval] at h3
    rw [hpdef]
    exact h3
  have hpderiv : ∀ x, deriv p x = deriv V x * p x - w x := fun x => (hp_has x).deriv
  have hp_left : ∀ x, x ≤ a → p x = m * Real.exp (V x) * ∫ s in Set.Iic x, ρ s := by
    intro x hx
    have hsplit : ∫ s in Set.Iic x, w s * ρ s = -m * ∫ s in Set.Iic x, ρ s := by
      have h1 : (fun s => w s * ρ s) =ᵐ[volume.restrict (Set.Iic x)] fun s => -(m * ρ s) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Iic] with s hs
        have hs' : u s = 0 := hu_le s (le_trans hs hx)
        simp only [hwdef, hs']
        ring
      rw [integral_congr_ae h1, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
        neg_mul]
    change -(Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s)
      = m * Real.exp (V x) * ∫ s in Set.Iic x, ρ s
    rw [hsplit]
    ring
  have hp_right : ∀ x, b ≤ x → p x = -m * Real.exp (V x) * ∫ s in Set.Ioi x, ρ s := by
    intro x hx
    have h2 : ∫ s in Set.Iic x, w s * ρ s = (∫ s, w s * ρ s) - (∫ s in Set.Ioi x, w s * ρ s) :=
      integral_Iic_eq _ hwρ_int x
    have h3 : ∫ s in Set.Ioi x, w s * ρ s = -m * ∫ s in Set.Ioi x, ρ s := by
      have h1 : (fun s => w s * ρ s) =ᵐ[volume.restrict (Set.Ioi x)] fun s => -(m * ρ s) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
        have hs' : u s = 0 := hu_ge s (le_trans hx (le_of_lt hs))
        simp only [hwdef, hs']
        ring
      rw [integral_congr_ae h1, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
        neg_mul]
    change -(Real.exp (V x) * ∫ s in Set.Iic x, w s * ρ s)
      = -m * Real.exp (V x) * ∫ s in Set.Ioi x, ρ s
    rw [h2, h3, hwmean, zero_sub]
    ring
  -- bound: |p| ≤ |m| / |V'| on the tails
  have htail_left : ∀ x, x ≤ a → Real.exp (V x) * ∫ s in Set.Iic x, ρ s ≤ 1 / (-deriv V x) := by
    intro x hx
    have hlt : deriv V x < 0 := lt_of_le_of_lt (hV'neg x hx) (by linarith)
    have htb := Commons.Analysis.Convex.integral_Iic_exp_neg_le V hVconv hVd hlt
    calc Real.exp (V x) * ∫ s in Set.Iic x, ρ s
        ≤ Real.exp (V x) * (Real.exp (-(V x)) / (-deriv V x)) :=
          mul_le_mul_of_nonneg_left htb (Real.exp_pos _).le
      _ = 1 / (-deriv V x) := by rw [← mul_div_assoc, hexpV x]
  have htail_right : ∀ x, b ≤ x → Real.exp (V x) * ∫ s in Set.Ioi x, ρ s ≤ 1 / deriv V x := by
    intro x hx
    have hpos : 0 < deriv V x := lt_of_lt_of_le hc₁ (hV'pos x hx)
    have htb := Commons.Analysis.Convex.integral_Ioi_exp_neg_le V hVconv hVd hpos
    calc Real.exp (V x) * ∫ s in Set.Ioi x, ρ s
        ≤ Real.exp (V x) * (Real.exp (-(V x)) / deriv V x) :=
          mul_le_mul_of_nonneg_left htb (Real.exp_pos _).le
      _ = 1 / deriv V x := by rw [← mul_div_assoc, hexpV x]
  have hp_le_left : ∀ x, x ≤ a → |p x| ≤ |m| / (-deriv V x) := by
    intro x hx
    have h1 := htail_left x hx
    have h6 : |p x| = |m| * (Real.exp (V x) * ∫ s in Set.Iic x, ρ s) := by
      rw [hp_left x hx, mul_assoc, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (integral_Iic_nonneg_of_nonneg hρnonneg x)]
    rw [h6]
    calc |m| * (Real.exp (V x) * ∫ s in Set.Iic x, ρ s) ≤ |m| * (1 / (-deriv V x)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg m)
      _ = |m| / (-deriv V x) := by rw [mul_one_div]
  have hp_le_right : ∀ x, b ≤ x → |p x| ≤ |m| / deriv V x := by
    intro x hx
    have h1 := htail_right x hx
    have h6 : |p x| = |m| * (Real.exp (V x) * ∫ s in Set.Ioi x, ρ s) := by
      rw [hp_right x hx, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (integral_Ioi_nonneg_of_nonneg hρnonneg x)]
      ring
    rw [h6]
    calc |m| * (Real.exp (V x) * ∫ s in Set.Ioi x, ρ s) ≤ |m| * (1 / deriv V x) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg m)
      _ = |m| / deriv V x := by rw [mul_one_div]
  have hp_bound_left : ∀ x, x ≤ a → |p x| ≤ |m| / c₂ := by
    intro x hx
    refine le_trans (hp_le_left x hx) ?_
    exact div_le_div_of_nonneg_left (abs_nonneg m) hc₂ (by linarith [hV'neg x hx])
  have hp_bound_right : ∀ x, b ≤ x → |p x| ≤ |m| / c₁ := by
    intro x hx
    refine le_trans (hp_le_right x hx) ?_
    exact div_le_div_of_nonneg_left (abs_nonneg m) hc₁ (by linarith [hV'pos x hx])
  -- bound: |V' p| ≤ max (BV * Bp) |m|
  obtain ⟨Bp, hBp⟩ := isCompact_Icc.exists_bound_of_continuousOn hpcont.continuousOn
  obtain ⟨BV, hBV⟩ := isCompact_Icc.exists_bound_of_continuousOn hV1c.continuousOn
  have hV'p_bound : ∀ x, |deriv V x * p x| ≤ max (BV * Bp) |m| := by
    intro x
    by_cases hx : x ≤ a
    · have hlt : deriv V x < 0 := lt_of_le_of_lt (hV'neg x hx) (by linarith)
      have h6 : |deriv V x * p x|
          = (-deriv V x) * (|m| * (Real.exp (V x) * ∫ s in Set.Iic x, ρ s)) := by
        rw [hp_left x hx]
        simp only [abs_mul, abs_of_neg hlt, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (integral_Iic_nonneg_of_nonneg hρnonneg x)]
        ring
      have h7 : (-deriv V x) * (|m| * (Real.exp (V x) * ∫ s in Set.Iic x, ρ s))
          ≤ (-deriv V x) * (|m| * (1 / (-deriv V x))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul_of_nonneg_left (htail_left x hx) (abs_nonneg m)
      have h8 : (-deriv V x) * (|m| * (1 / (-deriv V x))) = |m| :=
        arithC (ne_of_gt (by linarith : (0:ℝ) < -deriv V x))
      exact le_trans (le_of_eq h6) (le_trans h7 (le_of_eq h8)) |>.trans (le_max_right _ _)
    · by_cases hx2 : b ≤ x
      · have hpos : 0 < deriv V x := lt_of_lt_of_le hc₁ (hV'pos x hx2)
        have h6 : |deriv V x * p x|
            = deriv V x * (|m| * (Real.exp (V x) * ∫ s in Set.Ioi x, ρ s)) := by
          rw [hp_right x hx2]
          simp only [abs_mul, abs_neg, abs_of_pos hpos, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (integral_Ioi_nonneg_of_nonneg hρnonneg x)]
          ring
        have h7 : deriv V x * (|m| * (Real.exp (V x) * ∫ s in Set.Ioi x, ρ s))
            ≤ deriv V x * (|m| * (1 / deriv V x)) := by
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          exact mul_le_mul_of_nonneg_left (htail_right x hx2) (abs_nonneg m)
        have h8 : deriv V x * (|m| * (1 / deriv V x)) = |m| :=
          arithC (ne_of_gt hpos)
        exact le_trans (le_of_eq h6) (le_trans h7 (le_of_eq h8)) |>.trans (le_max_right _ _)
      · have hax : a ≤ x := le_of_lt (lt_of_not_ge hx)
        have hxb : x ≤ b := le_of_lt (lt_of_not_ge hx2)
        refine le_trans ?_ (le_max_left _ _)
        rw [abs_mul]
        exact mul_le_mul (hBV x ⟨hax, hxb⟩) (hBp x ⟨hax, hxb⟩) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hBV x ⟨hax, hxb⟩))
  set Btot : ℝ := max Bp (max (|m| / c₁) (|m| / c₂)) with hBtot
  have hp_bound : ∀ x, |p x| ≤ Btot := by
    intro x
    by_cases hx : x ≤ a
    · exact le_trans (hp_bound_left x hx) (le_trans (le_max_right _ _) (le_max_right _ _))
    · by_cases hx2 : b ≤ x
      · exact le_trans (hp_bound_right x hx2) (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (hBp x ⟨le_of_lt (lt_of_not_ge hx), le_of_lt (lt_of_not_ge hx2)⟩)
          (le_max_left _ _)
  set Bvp : ℝ := max (BV * Bp) |m| with hBvp
  have hBtot0 : 0 ≤ Btot := le_trans (abs_nonneg (p 0)) (hp_bound 0)
  have hw_has : ∀ x, HasDerivAt w (deriv u x) x := by
    intro x
    rw [hwdef]
    exact ((hu.differentiable (by norm_num) x).hasDerivAt.sub_const m)
  have hρd : ∀ x, HasDerivAt ρ (-(deriv V x) * ρ x) x := by
    intro x
    rw [hρdef]
    simpa [mul_comm] using (hVd x).hasDerivAt.neg.exp
  have hpderiv_cont : Continuous (deriv p) := by
    have h1 : deriv p = fun x => deriv V x * p x - w x := funext hpderiv
    rw [h1]
    exact (hV1c.mul hpcont).sub hwcont
  have hV'p2_int : Integrable (fun x => (deriv V x) ^ 2 * p x ^ 2 * ρ x) := by
    have hb : ∀ x, |deriv V x * p x| ≤ Bvp := fun x => by
      rw [hBvp]; exact hV'p_bound x
    have hbound : ∀ x, |(deriv V x) ^ 2 * p x ^ 2 * ρ x| ≤ Bvp ^ 2 * ρ x := by
      intro x
      have h2 : (deriv V x) ^ 2 * p x ^ 2 * ρ x = (deriv V x * p x) ^ 2 * ρ x := by ring
      have h4 : (deriv V x * p x) ^ 2 ≤ Bvp ^ 2 := by
        rw [← sq_abs (deriv V x * p x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
      rw [h2, abs_mul, abs_of_nonneg (hρnonneg x), abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right h4 (hρnonneg x)
    refine Integrable.mono' (hρint.const_mul (Bvp ^ 2))
      (((hV1c.pow 2).mul (hpcont.pow 2)).mul hρcont).aestronglyMeasurable ?_
    filter_upwards with x
    exact hbound x
  have hp'2ρ_int : Integrable (fun x => (deriv p x) ^ 2 * ρ x) := by
    have hb : ∀ x, |deriv V x * p x| ≤ Bvp := fun x => by
      rw [hBvp]; exact hV'p_bound x
    have hb' : ∀ x, |w x| ≤ B + |m| := by
      intro x
      simp only [hwdef]
      have h1 : |u x - m| ≤ |u x| + |m| := by simpa using abs_sub_le (u x) 0 m
      linarith [hB x]
    have hbd : ∀ x, |deriv p x| ≤ Bvp + (B + |m|) := by
      intro x
      rw [hpderiv x]
      have h1 : |deriv V x * p x - w x| ≤ |deriv V x * p x| + |w x| := by
        simpa using abs_sub_le (deriv V x * p x) 0 (w x)
      linarith [h1, hb x, hb' x]
    refine Integrable.mono' (hρint.const_mul ((Bvp + (B + |m|)) ^ 2)) ?_ ?_
    · exact ((hpderiv_cont.pow 2).mul hρcont).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg x), abs_of_nonneg (sq_nonneg _)]
      have h5 : (deriv p x) ^ 2 ≤ (Bvp + (B + |m|)) ^ 2 := by
        rw [← sq_abs (deriv p x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
      exact mul_le_mul_of_nonneg_right h5 (hρnonneg x)
  have hV'pp'_int : Integrable (fun x => (deriv V x * (p x * deriv p x)) * ρ x) := by
    have hb : ∀ x, |deriv V x * p x| ≤ Bvp := fun x => by
      rw [hBvp]; exact hV'p_bound x
    have hb' : ∀ x, |w x| ≤ B + |m| := by
      intro x
      simp only [hwdef]
      have h1 : |u x - m| ≤ |u x| + |m| := by simpa using abs_sub_le (u x) 0 m
      linarith [hB x]
    have hp' : ∀ x, |deriv p x| ≤ Bvp + (B + |m|) := by
      intro x
      rw [hpderiv x]
      have h1 : |deriv V x * p x - w x| ≤ |deriv V x * p x| + |w x| := by
        simpa using abs_sub_le (deriv V x * p x) 0 (w x)
      linarith [h1, hb x, hb' x]
    have hbound : ∀ x, |(deriv V x * (p x * deriv p x)) * ρ x|
        ≤ (Bvp * (Bvp + (B + |m|))) * ρ x := by
      intro x
      have h2 : |deriv V x * (p x * deriv p x)| ≤ Bvp * (Bvp + (B + |m|)) := by
        rw [abs_mul, abs_mul, ← mul_assoc, ← abs_mul]
        exact mul_le_mul (hb x) (hp' x) (abs_nonneg _) (le_trans (abs_nonneg _) (hb x))
      rw [abs_mul, abs_of_nonneg (hρnonneg x)]
      exact mul_le_mul_of_nonneg_right h2 (hρnonneg x)
    have hcont : Continuous (fun x => (deriv V x * (p x * deriv p x)) * ρ x) :=
      (hV1c.mul (hpcont.mul hpderiv_cont)).mul hρcont
    refine Integrable.mono' (hρint.const_mul (Bvp * (Bvp + (B + |m|))))
      hcont.aestronglyMeasurable ?_
    filter_upwards with x
    exact hbound x
  have hmid : Integrable (fun x => 2 * ((deriv V x * (p x * deriv p x)) * ρ x)) :=
    hV'pp'_int.const_mul 2
  have hV''p2ρ_int : Integrable (fun x => deriv (deriv V) x * p x ^ 2 * ρ x) := by
    have hle : ∀ x, x ≤ a → ‖deriv (deriv V) x * p x ^ 2 * ρ x‖
        ≤ m ^ 2 * (deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) := by
      intro x hx
      have hpx : |p x| ≤ |m| / (-deriv V x) := hp_le_left x hx
      have h1 : (p x) ^ 2 ≤ m ^ 2 / (deriv V x) ^ 2 := by
        rw [← sq_abs (p x)]
        calc |p x| ^ 2 ≤ (|m| / (-deriv V x)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpx 2
          _ = m ^ 2 / (deriv V x) ^ 2 := by rw [div_pow, sq_abs, neg_sq]
      have hV''0 : 0 ≤ deriv (deriv V) x := (hV2 x).le
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hV''0 (sq_nonneg _)) (hρnonneg x))]
      rw [show ρ x = Real.exp (-(V x)) from rfl]
      have h3 : deriv (deriv V) x * p x ^ 2 ≤ deriv (deriv V) x * (m ^ 2 / (deriv V x) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hV''0
      calc deriv (deriv V) x * p x ^ 2 * Real.exp (-(V x))
          ≤ deriv (deriv V) x * (m ^ 2 / (deriv V x) ^ 2) * Real.exp (-(V x)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = m ^ 2 * (deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) := by ring
    have hle' : ∀ x, b ≤ x → ‖deriv (deriv V) x * p x ^ 2 * ρ x‖
        ≤ m ^ 2 * (deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) := by
      intro x hx
      have hpx : |p x| ≤ |m| / deriv V x := hp_le_right x hx
      have h1 : (p x) ^ 2 ≤ m ^ 2 / (deriv V x) ^ 2 := by
        rw [← sq_abs (p x)]
        calc |p x| ^ 2 ≤ (|m| / deriv V x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpx 2
          _ = m ^ 2 / (deriv V x) ^ 2 := by rw [div_pow, sq_abs]
      have hV''0 : 0 ≤ deriv (deriv V) x := (hV2 x).le
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hV''0 (sq_nonneg _)) (hρnonneg x))]
      rw [show ρ x = Real.exp (-(V x)) from rfl]
      have h3 : deriv (deriv V) x * p x ^ 2 ≤ deriv (deriv V) x * (m ^ 2 / (deriv V x) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hV''0
      calc deriv (deriv V) x * p x ^ 2 * Real.exp (-(V x))
          ≤ deriv (deriv V) x * (m ^ 2 / (deriv V x) ^ 2) * Real.exp (-(V x)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = m ^ 2 * (deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2) := by ring
    have hIic : IntegrableOn (fun x => deriv (deriv V) x * p x ^ 2 * ρ x) (Set.Iic a) := by
      have hbase := Commons.Analysis.Convex.integrableOn_deriv2_exp_neg_div_sq V hV hVconv hc₂
        (fun x hx => hV'neg x hx)
      refine Integrable.mono' (hbase.const_mul (m ^ 2)) ?_ ?_
      · exact ((hV2c.mul (hpcont.pow 2)).mul hρcont).aestronglyMeasurable
      · filter_upwards [self_mem_ae_restrict measurableSet_Iic] with x hx
        exact hle x hx
    have hIci : IntegrableOn (fun x => deriv (deriv V) x * p x ^ 2 * ρ x) (Set.Ici b) := by
      have hbase := Commons.Analysis.Convex.integrableOn_deriv2_exp_neg_div_sq_Ici V hV hVconv hc₁
        (fun x hx => hV'pos x hx)
      refine Integrable.mono' (hbase.const_mul (m ^ 2)) ?_ ?_
      · exact ((hV2c.mul (hpcont.pow 2)).mul hρcont).aestronglyMeasurable
      · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
        exact hle' x hx
    have hIcc : IntegrableOn (fun x => deriv (deriv V) x * p x ^ 2 * ρ x) (Set.Icc a b) :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        ((hV2c.continuousOn.mul (hpcont.continuousOn.pow 2)).mul hρcont.continuousOn)
    have h1 := hIic.union hIcc
    rw [Set.Iic_union_Icc_eq_Iic hab] at h1
    have h4 := h1.union hIci
    rw [Set.Iic_union_Ici] at h4
    simpa [IntegrableOn] using h4
  -- Tendsto of ρ at ±∞
  have hρbot : Filter.Tendsto ρ Filter.atBot (𝓝 0) := by
    have h1 : Filter.Tendsto (fun x => -(V x)) Filter.atBot Filter.atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      filter_upwards [hVbot.eventually (Filter.eventually_ge_atTop (-b))] with x hx
      linarith
    exact Real.tendsto_exp_atBot.comp h1
  have hρtop : Filter.Tendsto ρ Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun x => -(V x)) Filter.atTop Filter.atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      filter_upwards [hVtop.eventually (Filter.eventually_ge_atTop (-b))] with x hx
      linarith
    exact Real.tendsto_exp_atBot.comp h1
  -- (D1)
  have hf_int : Integrable (fun x => deriv w x * p x * ρ x) := by
    have h3 : (fun x => deriv w x * p x * ρ x) = fun x => (deriv u x * p x) * ρ x := by
      funext x; rw [hwderiv x]
    rw [h3]
    obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous_hasCompactSupport
      (fun x => deriv u x * p x) (hducont.mul hpcont) (hducs.mul_right)
    have hcont : Continuous (fun x => deriv u x * p x * ρ x) := (hducont.mul hpcont).mul hρcont
    refine Integrable.mono' (hρint.const_mul C) hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg x)]
    exact mul_le_mul_of_nonneg_right (hC x) (hρnonneg x)
  have hD1 : ∫ x, deriv w x * p x * ρ x = ∫ x, w x ^ 2 * ρ x := by
    have hF : ∀ x, HasDerivAt (fun y => w y * p y * ρ y)
        (deriv w x * p x * ρ x - w x ^ 2 * ρ x) x := by
      intro x
      have hwp : HasDerivAt (fun y => w y * p y)
          (deriv u x * p x + w x * (deriv V x * p x - w x)) x :=
        (hw_has x).mul (hp_has x)
      have h3 := hwp.mul (hρd x)
      have hval : (deriv u x * p x + w x * (deriv V x * p x - w x)) * ρ x
          + (w x * p x) * (-(deriv V x) * ρ x) = deriv w x * p x * ρ x - w x ^ 2 * ρ x := by
        rw [hwderiv x]; ring
      rw [hval] at h3
      exact h3
    have hInt : Integrable (fun x => deriv w x * p x * ρ x - w x ^ 2 * ρ x) :=
      hf_int.sub hw2ρ_int
    have hbot : Filter.Tendsto (fun y => w y * p y * ρ y) Filter.atBot (𝓝 0) := by
      have hev : (fun y => w y * p y * ρ y) =ᶠ[Filter.atBot]
          fun y => -m ^ 2 * ∫ s in Set.Iic y, ρ s := by
        filter_upwards [Filter.eventually_le_atBot a] with y hy
        simp only [hp_left y hy, hwdef, hu_le y hy]
        rw [zero_sub]
        have hkey : Real.exp (V y) * ρ y = 1 := hexpV y
        calc (-m) * (m * Real.exp (V y) * ∫ s in Set.Iic y, ρ s) * ρ y
            = -m ^ 2 * (Real.exp (V y) * ρ y) * ∫ s in Set.Iic y, ρ s := by ring
          _ = -m ^ 2 * ∫ s in Set.Iic y, ρ s := by rw [hkey, mul_one]
      refine Filter.Tendsto.congr' hev.symm ?_
      have h1 := tendsto_integral_Iic_zero (μ := volume) (f := ρ) (a := fun y : ℝ => y) tendsto_id
      simpa using h1.const_mul (-m ^ 2)
    have htop : Filter.Tendsto (fun y => w y * p y * ρ y) Filter.atTop (𝓝 0) := by
      have hev : (fun y => w y * p y * ρ y) =ᶠ[Filter.atTop]
          fun y => m ^ 2 * ∫ s in Set.Ioi y, ρ s := by
        filter_upwards [Filter.eventually_ge_atTop b] with y hy
        simp only [hp_right y hy, hwdef, hu_ge y hy]
        rw [zero_sub]
        have hkey : Real.exp (V y) * ρ y = 1 := hexpV y
        calc (-m) * (-m * Real.exp (V y) * ∫ s in Set.Ioi y, ρ s) * ρ y
            = m ^ 2 * (Real.exp (V y) * ρ y) * ∫ s in Set.Ioi y, ρ s := by ring
          _ = m ^ 2 * ∫ s in Set.Ioi y, ρ s := by rw [hkey, mul_one]
      refine Filter.Tendsto.congr' hev.symm ?_
      have h1 := tendsto_integral_Ioi_zero (μ := volume) (f := ρ) (b := fun y : ℝ => y) tendsto_id
      simpa using h1.const_mul (m ^ 2)
    have h0 := MeasureTheory.integral_of_hasDerivAt_of_tendsto hF hInt hbot htop
    have hsimp : ∫ x, deriv w x * p x * ρ x - w x ^ 2 * ρ x
        = (∫ x, deriv w x * p x * ρ x) - ∫ x, w x ^ 2 * ρ x := by
      rw [show (fun x => deriv w x * p x * ρ x - w x ^ 2 * ρ x)
          = (fun x => deriv w x * p x * ρ x) - (fun x => w x ^ 2 * ρ x) from by
        funext x; rfl]
      rw [MeasureTheory.integral_sub' hf_int hw2ρ_int]
    rw [hsimp, sub_self] at h0
    linarith
  -- (D2)
  have hD2 : ∫ x, (deriv (deriv V) x * p x ^ 2 * ρ x
        + 2 * ((deriv V x * (p x * deriv p x)) * ρ x) - (deriv V x) ^ 2 * p x ^ 2 * ρ x) = 0 := by
    have hF : ∀ x, HasDerivAt (fun y => deriv V y * p y ^ 2 * ρ y)
        (deriv (deriv V) x * p x ^ 2 * ρ x + 2 * ((deriv V x * (p x * deriv p x)) * ρ x)
          - (deriv V x) ^ 2 * p x ^ 2 * ρ x) x := by
      intro x
      have h1 : HasDerivAt (fun y => deriv V y) (deriv (deriv V) x) x := (hV1d x).hasDerivAt
      have h2 : HasDerivAt (fun y => p y ^ 2) (2 * p x * deriv p x) x := by
        have h := (hp_has x).pow 2
        have hval : (↑(2 : ℕ) : ℝ) * p x ^ ((2 : ℕ) - 1) * (deriv V x * p x - w x)
            = 2 * p x * deriv p x := by
          rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, hpderiv x]
          norm_num
        rw [hval] at h
        exact h
      have h3 := (h1.mul h2).mul (hρd x)
      simp only [Pi.mul_apply] at h3
      have hval : (deriv (deriv V) x * p x ^ 2 + deriv V x * (2 * p x * deriv p x)) * ρ x
          + deriv V x * p x ^ 2 * (-(deriv V x) * ρ x)
          = deriv (deriv V) x * p x ^ 2 * ρ x + 2 * ((deriv V x * (p x * deriv p x)) * ρ x)
            - (deriv V x) ^ 2 * p x ^ 2 * ρ x := by ring
      rw [hval] at h3
      exact h3
    have hAB := hV''p2ρ_int.add hmid
    have hInt : Integrable (fun x => deriv (deriv V) x * p x ^ 2 * ρ x
        + 2 * ((deriv V x * (p x * deriv p x)) * ρ x) - (deriv V x) ^ 2 * p x ^ 2 * ρ x) :=
      hAB.sub hV'p2_int
    have hbound : ∀ y, ‖deriv V y * p y ^ 2 * ρ y‖ ≤ (Bvp * Btot) * ρ y := by
      intro y
      have h1 : |deriv V y * p y| ≤ Bvp := by rw [hBvp]; exact hV'p_bound y
      have h2 : |p y| ≤ Btot := hp_bound y
      have h4 : deriv V y * p y ^ 2 * ρ y = (deriv V y * p y) * p y * ρ y := by ring
      rw [h4, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρnonneg y)]
      calc |deriv V y * p y| * |p y| * ρ y ≤ (Bvp * Btot) * ρ y := by
            refine mul_le_mul_of_nonneg_right ?_ (hρnonneg y)
            exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        _ = (Bvp * Btot) * ρ y := rfl
    have hbot : Filter.Tendsto (fun y => deriv V y * p y ^ 2 * ρ y) Filter.atBot (𝓝 0) :=
      squeeze_zero_norm' (Filter.Eventually.of_forall hbound)
        (by simpa using hρbot.const_mul (Bvp * Btot))
    have htop : Filter.Tendsto (fun y => deriv V y * p y ^ 2 * ρ y) Filter.atTop (𝓝 0) :=
      squeeze_zero_norm' (Filter.Eventually.of_forall hbound)
        (by simpa using hρtop.const_mul (Bvp * Btot))
    simpa using MeasureTheory.integral_of_hasDerivAt_of_tendsto hF hInt hbot htop
  -- (D3)
  have hD2' : ∫ x, (deriv V x) ^ 2 * p x ^ 2 * ρ x
      = (∫ x, deriv (deriv V) x * p x ^ 2 * ρ x)
        + 2 * (∫ x, (deriv V x * (p x * deriv p x)) * ρ x) := by
    have hAB : Integrable (fun x => deriv (deriv V) x * p x ^ 2 * ρ x) := hV''p2ρ_int
    have hkey := integral_sum_sub hAB hmid hV'p2_int
    have hmid' : ∫ x, 2 * ((deriv V x * (p x * deriv p x)) * ρ x)
        = 2 * (∫ x, (deriv V x * (p x * deriv p x)) * ρ x) :=
      MeasureTheory.integral_const_mul 2 _
    rw [hkey, hmid'] at hD2
    linarith [hD2]
  have hA : ∫ x, w x ^ 2 * ρ x
      = ((∫ x, (deriv V x) ^ 2 * p x ^ 2 * ρ x)
        - 2 * (∫ x, (deriv V x * (p x * deriv p x)) * ρ x))
        + (∫ x, (deriv p x) ^ 2 * ρ x) := by
    have hpoint : ∀ x, w x ^ 2 * ρ x
        = ((deriv V x) ^ 2 * p x ^ 2 * ρ x - 2 * ((deriv V x * (p x * deriv p x)) * ρ x))
          + (deriv p x) ^ 2 * ρ x := by
      intro x
      have hw : w x = deriv V x * p x - deriv p x := by linarith [hpderiv x]
      rw [hw]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => hpoint x))]
    have hkey := integral_sub_add hV'p2_int hmid hp'2ρ_int
    have hmid' : ∫ x, 2 * ((deriv V x * (p x * deriv p x)) * ρ x)
        = 2 * (∫ x, (deriv V x * (p x * deriv p x)) * ρ x) :=
      MeasureTheory.integral_const_mul 2 _
    rw [hkey, hmid']
  have hCA : ∫ x, deriv (deriv V) x * p x ^ 2 * ρ x ≤ ∫ x, w x ^ 2 * ρ x := by
    have hp2 : 0 ≤ ∫ x, (deriv p x) ^ 2 * ρ x :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hρnonneg x))
    linarith [hA, hD2', hp2]
  -- (D4)
  have hCS : (∫ x, deriv u x * (p x * ρ x)) ^ 2
      ≤ (∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * ρ x)
        * (∫ x, deriv (deriv V) x * p x ^ 2 * ρ x) := by
    have ha : Integrable (fun x => (deriv u x / Real.sqrt (deriv (deriv V) x)) ^ 2 * ρ x) := by
      refine hud_int.congr (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      rw [div_pow, Real.sq_sqrt (hV2 x).le]
    have hb : Integrable (fun x => (p x * Real.sqrt (deriv (deriv V) x)) ^ 2 * ρ x) := by
      refine hV''p2ρ_int.congr (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      rw [mul_pow, Real.sq_sqrt (hV2 x).le]
      ring
    have h := Commons.Analysis.Integral.sq_integral_mul_le_integral_sq_mul
      (fun x => deriv u x / Real.sqrt (deriv (deriv V) x))
      (fun x => p x * Real.sqrt (deriv (deriv V) x)) ρ hρnonneg ha hb
    have h1 : ∫ x, (deriv u x / Real.sqrt (deriv (deriv V) x))
        * (p x * Real.sqrt (deriv (deriv V) x)) * ρ x = ∫ x, deriv u x * (p x * ρ x) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      have hx : Real.sqrt (deriv (deriv V) x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hV2 x))
      have key : (deriv u x / Real.sqrt (deriv (deriv V) x))
          * (p x * Real.sqrt (deriv (deriv V) x)) * ρ x = deriv u x * (p x * ρ x) := by
        field_simp
      rw [key]
    have h2 : ∫ x, (deriv u x / Real.sqrt (deriv (deriv V) x)) ^ 2 * ρ x
        = ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * ρ x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      rw [div_pow, Real.sq_sqrt (hV2 x).le]
    have h3 : ∫ x, (p x * Real.sqrt (deriv (deriv V) x)) ^ 2 * ρ x
        = ∫ x, deriv (deriv V) x * p x ^ 2 * ρ x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      rw [mul_pow, Real.sq_sqrt (hV2 x).le]
      ring
    rwa [h1, h2, h3] at h
  -- (D5)
  have hD : ∫ x, deriv u x * (p x * ρ x) = ∫ x, w x ^ 2 * ρ x := by
    rw [← hD1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hwderiv x]
    ring
  have hDnonneg : 0 ≤ ∫ x, w x ^ 2 * ρ x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hρnonneg x))
  have hBnonneg : 0 ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * ρ x :=
    integral_nonneg (fun x => mul_nonneg (div_nonneg (sq_nonneg _) (hV2 x).le) (hρnonneg x))
  rw [hD] at hCS
  nlinarith [hCS, hCA, hDnonneg, hBnonneg]

/-- **Sharp one-dimensional Brascamp–Lieb inequality.** -/
theorem brascamp_lieb_one_dim_sharp (V u : ℝ → ℝ)
    (hV : ContDiff ℝ 2 V) (hVconv : ConvexOn ℝ Set.univ V)
    (hV2 : ∀ x, 0 < deriv (deriv V) x)
    (hVtop : Filter.Tendsto V Filter.atTop Filter.atTop)
    (hVbot : Filter.Tendsto V Filter.atBot Filter.atTop)
    (hu : ContDiff ℝ 1 u)
    (hu1 : Integrable fun x => u x * Real.exp (-(V x)))
    (hu2 : Integrable fun x => u x ^ 2 * Real.exp (-(V x)))
    (huw : Integrable fun x => u x ^ 2 / deriv (deriv V) x * Real.exp (-(V x)))
    (hud : Integrable fun x => (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x))) :
    (∫ x, u x ^ 2 * Real.exp (-(V x)))
        - (∫ x, u x * Real.exp (-(V x))) ^ 2 / (∫ x, Real.exp (-(V x)))
      ≤ ∫ x, (deriv u x) ^ 2 / deriv (deriv V) x * Real.exp (-(V x)) :=
  sharp_general_of_compactSupport
    (fun V u hV hVconv hV2 hVtop hVbot hu huK =>
      sharp_compact_aux V u hV hVconv hV2 hVtop hVbot hu huK)
    V u hV hVconv hV2 hVtop hVbot hu hu1 hu2 huw hud

end

end Commons.Analysis.Convex
