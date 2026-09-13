import Mathlib
import Submission.Commons.Analysis.Harmonic.sphereAverage_harmonic_C2
import Submission.Commons.Analysis.Harmonic.radial_mollification_sphere_average
import Submission.Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_three_le
import Submission.Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball

/-!
# Uniform quadratic approximation of a bounded harmonic function on the unit ball

A `C²` harmonic function `h` on the unit ball of `ℝ⁴` with `|h| ≤ 1` admits a quadratic
approximation by a trace-free quadratic form (plus a linear form and a constant) with error
`O(θ³)` on the closed ball of radius `θ`, *uniformly in* `θ ≤ 1 / 2`.

The proof uses a **fixed** radial mollifying kernel `kernel` (supported in the annulus
`1/32 < ‖y‖ < 1/8`) together with a **fixed** smooth cut-off `chi` which is `1` on the closed
ball of radius `3/4` and vanishes outside the unit ball.  With `ht = chi * h`, the sphere mean
value property of `h` implies that `(ht ⋆ kernel) x = (∫ kernel) * h x` for every `x` with
`‖x‖ ≤ 5/8`.  Hence `h` agrees near the closed ball of radius `1/2` with the smooth function
`F = (∫ kernel)⁻¹ • (ht ⋆ kernel)`, and the standard bound for the iterated derivatives of a
convolution gives the uniform bound `‖D³h‖ ≤ K` there.  Taylor's theorem with integral
remainder then yields the claim.
-/

noncomputable section

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal ContDiff
  Convolution

namespace Commons.Analysis.Harmonic

set_option linter.style.haveILetI false

/-! ## The fixed radial mollifying kernel and the fixed cut-off -/

/-- The radius of the support of the mollifying kernel. -/
private def sR : ℝ := 1 / 8

/-- The scale of the mollifying kernel; `sC * sR = 4`. -/
private def sC : ℝ := 32

/-- A smooth radial profile vanishing on `(-∞, 1]`, equal to `1` on `[2, 3]` and vanishing on
`[4, ∞)`. -/
private def sProfile : ℝ → ℝ :=
  fun s => Real.smoothTransition (s - 1) * Real.smoothTransition (4 - s)

/-- A smooth radial kernel supported in the annulus `sR / 4 < ‖y‖ < sR`. -/
private def sKer {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sProfile (sC * ‖y‖)

/-- A smooth cut-off equal to `1` on `closedBall 0 (3 / 4)` and vanishing outside `ball 0 1`. -/
private def sCut {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition (4 - 4 * ‖y‖)

section Basic

private lemma sR_pos : 0 < sR := by norm_num [sR]

private lemma sC_pos : 0 < sC := by norm_num [sC]

private lemma sC_mul_sR : sC * sR = 4 := by norm_num [sC, sR]

private lemma sC_mul_quarter : sC * (sR / 4) = 1 := by norm_num [sC, sR]

end Basic

/-! ## Smoothness of the radial profiles -/

/-- The radial function `y ↦ smoothTransition (k - c * ‖y‖)` is smooth on any inner product space
when `1 < k` and `0 < c`: near the origin it is identically `1`, and away from the origin it is the
composition of the smooth function `t ↦ smoothTransition (k - c * t)` with the norm. -/
private lemma contDiff_smoothTransition_sub_mul_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c k : ℝ} (hc : 0 < c) (hk : 1 < k) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Real.smoothTransition (k - c * ‖y‖)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E)
      (show (0 : ℝ) < (k - 1) / c by positivity)] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    refine Real.smoothTransition.one_of_one_le ?_
    have hcy : c * ‖y‖ < k - 1 := by
      have h := (lt_div_iff₀ hc).mp hy
      rw [mul_comm] at h
      exact h
    linarith
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition (k - c * t)) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id))
    exact h1.contDiffAt.comp x (contDiffAt_norm (E := E) ℝ hx)

private lemma sProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) sProfile := by
  unfold sProfile
  fun_prop

private lemma sProfile_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) : sProfile t = 0 := by
  simp only [sProfile, Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0),
    zero_mul]

private lemma sProfile_eq_zero_of_ge_four {t : ℝ} (ht : 4 ≤ t) : sProfile t = 0 := by
  simp only [sProfile, Real.smoothTransition.zero_of_nonpos (by linarith : 4 - t ≤ 0),
    mul_zero]

private lemma sProfile_ne_zero {t : ℝ} (h1 : 1 < t) (h2 : t < 4) : sProfile t ≠ 0 := by
  refine mul_ne_zero (ne_of_gt (Real.smoothTransition.pos_of_pos (by linarith)))
    (ne_of_gt (Real.smoothTransition.pos_of_pos (by linarith)))

private lemma sProfile_eq_one {t : ℝ} (h1 : 2 ≤ t) (h2 : t ≤ 3) : sProfile t = 1 := by
  simp only [sProfile, Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - 1),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 - t), mul_one]

/-! ## Properties of the mollifying kernel -/

section Kernel

variable {n : ℕ}

private lemma sKer_eq_zero_left {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ≤ sR / 4) :
    sKer y = 0 := by
  refine sProfile_eq_zero_of_le_one ?_
  have h1 : sC * ‖y‖ ≤ sC * (sR / 4) := mul_le_mul_of_nonneg_left hy sC_pos.le
  rw [sC_mul_quarter] at h1
  linarith

private lemma sKer_eq_zero {y : EuclideanSpace ℝ (Fin n)} (hy : sR ≤ ‖y‖) :
    sKer y = 0 := by
  refine sProfile_eq_zero_of_ge_four ?_
  have h1 : sC * sR ≤ sC * ‖y‖ := mul_le_mul_of_nonneg_left hy sC_pos.le
  rw [sC_mul_sR] at h1
  linarith

private lemma sKer_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) => sKer y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n))
      (show (0 : ℝ) < sR / 4 by norm_num [sR])] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact sKer_eq_zero_left (le_of_lt hy)
  · have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => sProfile (sC * ‖y‖)) x := by
      have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => sProfile (sC * s)) ‖x‖ :=
        (sProfile_contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt
      exact h3.comp x (contDiffAt_norm ℝ hx)
    simpa only [sKer] using h2

private lemma sKer_nonneg (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ sKer y := by
  simp only [sKer, sProfile]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private lemma sKer_le_one (y : EuclideanSpace ℝ (Fin n)) : sKer y ≤ 1 := by
  simp only [sKer, sProfile]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

private lemma sKer_even (y : EuclideanSpace ℝ (Fin n)) : sKer (-y) = sKer y := by
  simp only [sKer, norm_neg]

private lemma sKer_rad :
    ∀ (r : ℝ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1), 0 < r →
      sKer (r • (v : EuclideanSpace ℝ (Fin n))) = sProfile (sC * r) := by
  intro r v hr
  simp only [sKer, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp v.2, mul_one]

private lemma sKer_tsupport :
    tsupport (sKer (n := n)) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) sR := by
  intro y hy
  by_contra hcon
  rw [mem_closedBall, dist_zero_right, not_le] at hcon
  rw [tsupport, Metric.mem_closure_iff] at hy
  obtain ⟨z, hzs, hzd⟩ := hy ((‖y‖ - sR) / 2) (by linarith)
  rw [Function.mem_support, ne_eq] at hzs
  rw [dist_eq_norm] at hzd
  have h1 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    have := norm_add_le (y - z) z
    rwa [sub_add_cancel] at this
  exact hzs (sKer_eq_zero (by linarith))

private lemma sKer_hasCompactSupport :
    HasCompactSupport (sKer (n := n)) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) sR).of_isClosed_subset
    (isClosed_tsupport _) sKer_tsupport

private lemma sKer_integral_pos (hn : 0 < n) :
    0 < ∫ y : EuclideanSpace ℝ (Fin n), sKer y := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => sKer y) := sKer_contDiff.continuous
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => sKer y) volume :=
    hcont.integrable_of_hasCompactSupport sKer_hasCompactSupport
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set y₀ : EuclideanSpace ℝ (Fin n) := (1 / 16 : ℝ) • EuclideanSpace.single i0 1 with hy0
  have hy0n : ‖y₀‖ = 1 / 16 := by
    rw [hy0, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    norm_num
  refine integral_pos_of_integrable_nonneg_nonzero (x := y₀) hcont hint
    (fun y => sKer_nonneg y) ?_
  have hval : sKer y₀ = sProfile 2 := by
    simp only [sKer, hy0n, sC]; norm_num
  rw [hval, sProfile_eq_one (by norm_num) (by norm_num)]
  norm_num

end Kernel

/-! ## Properties of the cut-off -/

section Cutoff

variable {n : ℕ}

private lemma sCut_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) => sCut y) :=
  contDiff_smoothTransition_sub_mul_norm (E := EuclideanSpace ℝ (Fin n))
    (c := (4 : ℝ)) (k := (4 : ℝ)) (by norm_num) (by norm_num)

private lemma sCut_nonneg (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ sCut y :=
  Real.smoothTransition.nonneg _

private lemma sCut_le_one (y : EuclideanSpace ℝ (Fin n)) : sCut y ≤ 1 :=
  Real.smoothTransition.le_one _

private lemma sCut_eq_one {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ≤ 3 / 4) : sCut y = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have h : (4 : ℝ) * ‖y‖ ≤ 4 * (3 / 4) := mul_le_mul_of_nonneg_left hy (by norm_num)
  linarith

private lemma sCut_eq_zero {y : EuclideanSpace ℝ (Fin n)} (hy : 1 ≤ ‖y‖) : sCut y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h : (4 : ℝ) * 1 ≤ 4 * ‖y‖ := mul_le_mul_of_nonneg_left hy (by norm_num)
  linarith

private lemma sCut_support_subset :
    Function.support (sCut (n := n)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  intro y hy
  rw [Function.mem_support] at hy
  rw [mem_ball, dist_zero_right]
  by_contra hcon
  rw [not_lt] at hcon
  exact hy (sCut_eq_zero hcon)

private lemma sCut_hasCompactSupport :
    HasCompactSupport (sCut (n := n)) := by
  have hsupp : tsupport (sCut (n := n)) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [tsupport]
    exact closure_minimal (subset_trans sCut_support_subset ball_subset_closedBall)
      isClosed_closedBall
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
    (isClosed_tsupport _) hsupp

end Cutoff


/-! ## The main theorem -/

theorem quadratic_approx_of_harmonic_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : EuclideanSpace ℝ (Fin 4) → ℝ) (θ : ℝ), 0 < θ → θ ≤ 1 / 2 →
      ContDiffOn ℝ 2 h (Metric.ball 0 1) →
      (∀ x ∈ Metric.ball 0 1, Laplacian.laplacian h x = 0) →
      (∀ x ∈ Metric.ball 0 1, |h x| ≤ 1) →
      ∃ (Q : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ)
        (q : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) (t : ℝ),
        (∑ i : Fin 4, Q (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) ∧
        ∀ x ∈ Metric.closedBall 0 θ, |h x - (1 / 2 * Q x x + q x + t)| ≤ C * θ ^ 3 := by
  have hZpos : 0 < ∫ y : EuclideanSpace ℝ (Fin 4), sKer y :=
    sKer_integral_pos (n := 4) (by norm_num)
  have hZne : (∫ y : EuclideanSpace ℝ (Fin 4), sKer y) ≠ 0 := ne_of_gt hZpos
  refine ⟨max ((∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹
      * ∫ u : EuclideanSpace ℝ (Fin 4), ‖iteratedFDeriv ℝ 3 (sKer (n := 4)) u‖) 1,
    lt_max_of_lt_right zero_lt_one, ?_⟩
  intro h θ hθ hθhalf hh hΔ hb
  -- the truncated function
  let ht : EuclideanSpace ℝ (Fin 4) → ℝ := fun y => sCut y * h y
  have hcut_cont : Continuous (sCut (n := 4)) := sCut_contDiff.continuous
  have ht_le_chi : ∀ y : EuclideanSpace ℝ (Fin 4), ‖ht y‖ ≤ ‖sCut y‖ := by
    intro y
    by_cases hy : sCut y = 0
    · rw [show ht y = sCut y * h y from rfl, hy, zero_mul]
    · have hyball : y ∈ ball (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
        sCut_support_subset (Function.mem_support.mpr hy)
      have hyb : ‖h y‖ ≤ 1 := by
        rw [Real.norm_eq_abs]; exact hb y hyball
      rw [show ht y = sCut y * h y from rfl, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hyb
  have ht_bound : ∀ y : EuclideanSpace ℝ (Fin 4), ‖ht y‖ ≤ 1 := by
    intro y
    refine (ht_le_chi y).trans ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [sCut_nonneg y], sCut_le_one y⟩
  have ht_cont : Continuous ht := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx0 : sCut x = 0
    · have hx0' : ht x = 0 := by
        rw [show ht x = sCut x * h x from rfl, hx0, zero_mul]
      have hsq : Tendsto (fun y : EuclideanSpace ℝ (Fin 4) => ‖ht y‖) (𝓝 x) (𝓝 0) := by
        refine squeeze_zero (fun y => norm_nonneg _) (fun y => ht_le_chi y) ?_
        have h2 : Tendsto (fun y : EuclideanSpace ℝ (Fin 4) => ‖sCut y‖) (𝓝 x)
            (𝓝 ‖sCut x‖) := hcut_cont.norm.continuousAt
        rw [hx0, norm_zero] at h2
        exact h2
      have htend : Tendsto ht (𝓝 x) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsq
      change Tendsto ht (𝓝 x) (𝓝 (ht x))
      rw [hx0']
      exact htend
    · have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
        sCut_support_subset (Function.mem_support.mpr hx0)
      have hcx : ContinuousAt h x := hh.continuousOn.continuousAt (isOpen_ball.mem_nhds hxball)
      exact hcut_cont.continuousAt.mul hcx
  have ht_cs : HasCompactSupport ht :=
    sCut_hasCompactSupport.mul_right
  have ht_int : Integrable ht volume := ht_cont.integrable_of_hasCompactSupport ht_cs
  have ht_locint : LocallyIntegrable ht volume := ht_int.locallyIntegrable
  -- the mean value property of `h`
  have hMVP : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 4)) 1, ∀ r : ℝ, 0 < r →
      closedBall x r ⊆ ball 0 1 →
      (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
          h (x + r • (v : EuclideanSpace ℝ (Fin 4))) ∂MeasureTheory.volume.toSphere)
        = (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
            (1 : ℝ) ∂MeasureTheory.volume.toSphere) * h x := by
    intro x _ r hr hsub
    refine sphereAverage_harmonic_C2 (n := 4) (by norm_num) hr (hh.mono ?_) (fun y hy => hΔ y ?_) ?_
    · exact subset_trans ball_subset_closedBall hsub
    · exact subset_trans ball_subset_closedBall hsub hy
    · exact (hh.mono hsub).continuousOn
  -- the radial profile of the kernel
  have hφcont : Continuous (fun r : ℝ => sProfile (sC * r)) :=
    sProfile_contDiff.continuous.comp (continuous_const.mul continuous_id)
  have hφsupp : tsupport (fun r : ℝ => sProfile (sC * r)) ⊆ Icc 0 sR := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro r hr
    rw [Function.mem_support, ne_eq] at hr
    rw [mem_Icc]
    constructor
    · by_contra hcon
      rw [not_le] at hcon
      have h2 : sC * r < 0 := mul_neg_of_pos_of_neg sC_pos hcon
      exact hr (sProfile_eq_zero_of_le_one (by linarith))
    · by_contra hcon
      rw [not_le] at hcon
      have h2 : sC * sR ≤ sC * r := mul_le_mul_of_nonneg_left hcon.le sC_pos.le
      rw [sC_mul_sR] at h2
      exact hr (sProfile_eq_zero_of_ge_four h2)
  -- the mollification identity
  have hmoll : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ 5 / 8 →
      (∫ y : EuclideanSpace ℝ (Fin 4), h (x + y) * sKer y)
        = (∫ y : EuclideanSpace ℝ (Fin 4), sKer y) * h x := by
    intro x hx
    refine radial_mollification_sphere_average (n := 4) (by norm_num) sR_pos hh.continuousOn hMVP
      sKer_contDiff.continuous sKer_tsupport hφcont hφsupp sKer_rad ?_
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_zero_right]
    calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
          have h1 := norm_add_le (y - x) x
          rwa [sub_add_cancel] at h1
      _ ≤ sR + 5 / 8 := add_le_add hy hx
      _ < 1 := by norm_num [sR]
  -- the identification of `h` with a convolution
  let G : EuclideanSpace ℝ (Fin 4) → ℝ :=
    fun x => (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (sKer (n := 4))) x
  let F : EuclideanSpace ℝ (Fin 4) → ℝ := (∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹ • G
  have hconv : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ 5 / 8 → h x = F x := by
    intro x hx
    have hA : (∫ t : EuclideanSpace ℝ (Fin 4), ht t * sKer (x - t))
        = ∫ t : EuclideanSpace ℝ (Fin 4), ht (x - t) * sKer t := by
      have h1 := integral_sub_left_eq_self
        (fun u : EuclideanSpace ℝ (Fin 4) => ht (x - u) * sKer u) volume x
      rwa [show (fun u : EuclideanSpace ℝ (Fin 4) => ht (x - (x - u)) * sKer (x - u))
          = (fun u : EuclideanSpace ℝ (Fin 4) => ht u * sKer (x - u)) from by
            funext u; rw [show x - (x - u) = u from by abel]] at h1
    have hB : (∫ t : EuclideanSpace ℝ (Fin 4), ht (x - t) * sKer t)
        = ∫ t : EuclideanSpace ℝ (Fin 4), h (x - t) * sKer t := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [show ht (x - t) = sCut (x - t) * h (x - t) from rfl]
      by_cases hk : sKer t = 0
      · rw [hk, mul_zero, mul_zero]
      · have htmem : t ∈ tsupport (sKer (n := 4)) :=
          subset_tsupport _ (Function.mem_support.mpr hk)
        have htnorm : ‖t‖ ≤ sR := by
          have h1 := sKer_tsupport htmem
          rwa [mem_closedBall, dist_zero_right] at h1
        have hcut1 : sCut (x - t) = 1 := by
          refine sCut_eq_one ?_
          calc ‖x - t‖ ≤ ‖x‖ + ‖t‖ := norm_sub_le x t
            _ ≤ 5 / 8 + sR := add_le_add hx htnorm
            _ ≤ 3 / 4 := by norm_num [sR]
        rw [hcut1, one_mul]
    have hC : (∫ t : EuclideanSpace ℝ (Fin 4), h (x - t) * sKer t)
        = ∫ t : EuclideanSpace ℝ (Fin 4), h (x + t) * sKer t := by
      have h0 := integral_neg_eq_self
        (fun u : EuclideanSpace ℝ (Fin 4) => h (x + u) * sKer u) volume
      have h1 : (∫ u : EuclideanSpace ℝ (Fin 4), h (x - u) * sKer u)
          = ∫ u : EuclideanSpace ℝ (Fin 4), h (x + -u) * sKer (-u) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show h (x - u) * sKer u = h (x + -u) * sKer (-u)
        rw [show x - u = x + -u from sub_eq_add_neg x u, sKer_even]
      rw [h1, h0]
    have hstep : G x = (∫ y : EuclideanSpace ℝ (Fin 4), sKer y) * h x := by
      show (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (sKer (n := 4))) x = _
      rw [MeasureTheory.convolution_lsmul]
      simp only [smul_eq_mul]
      rw [hA, hB, hC, hmoll x hx]
    show h x = F x
    change h x = (∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹ * G x
    rw [hstep, ← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
  -- smoothness of `F`
  have hS : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 4) =>
        (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (sKer (n := 4))) x) :=
    sKer_hasCompactSupport.contDiff_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) ht_locint sKer_contDiff
  have hF_cd : ContDiff ℝ (⊤ : ℕ∞) F :=
    hS.const_smul ((∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹)
  have hF_at3 : ∀ x : EuclideanSpace ℝ (Fin 4), ContDiffAt ℝ 3 F x :=
    fun x => (hF_cd.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hident_ev : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ 1 / 2 → h =ᶠ[𝓝 x] F := by
    intro x hx
    have hε : 0 < 5 / 8 - ‖x‖ := by linarith
    filter_upwards [Metric.closedBall_mem_nhds x hε] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hy' : ‖y‖ ≤ 5 / 8 := by
      calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            have h1 := norm_add_le (y - x) x
            rwa [sub_add_cancel] at h1
        _ ≤ (5 / 8 - ‖x‖) + ‖x‖ := add_le_add hy le_rfl
        _ = 5 / 8 := by ring
    exact hconv y hy'
  -- the third derivative bound
  have hiter_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin 4) => iteratedFDeriv ℝ 3 (sKer (n := 4)) y) volume :=
    ((sKer_contDiff.continuous_iteratedFDeriv (m := 3)
      (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      (sKer_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) 3))
  have hbdd3 : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ 3 h x‖
        ≤ (∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹
          * ∫ u : EuclideanSpace ℝ (Fin 4), ‖iteratedFDeriv ℝ 3 (sKer (n := 4)) u‖ := by
    intro x hx
    have hieq : iteratedFDeriv ℝ 3 h x = iteratedFDeriv ℝ 3 F x :=
      ((hident_ev x hx).iteratedFDeriv ℝ 3).eq_of_nhds
    rw [hieq]
    have hsmul : iteratedFDeriv ℝ 3 F x
        = (∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹ •
            iteratedFDeriv ℝ 3 G x := by
      have h1 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := 3)
        (a := (∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹) (f := G) (x := x)
        ((hS.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top))
      simpa only [F] using h1
    rw [hsmul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hZpos.le)]
    have h2 : iteratedFDeriv ℝ 3 G x = (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => iteratedFDeriv ℝ 3 (sKer (n := 4)) y)) x :=
      congrFun (Commons.Analysis.Calculus.BumpFunction.iteratedFDeriv_convolution_lsmul
        (μ := volume) (f := ht) (g := sKer (n := 4))
        ht_locint sKer_contDiff sKer_hasCompactSupport 3) x
    rw [h2]
    exact mul_le_mul_of_nonneg_left
      (Commons.Analysis.Calculus.BumpFunction.norm_convolution_lsmul_le_integral
        (μ := volume) ht_bound hiter_int x)
      (inv_nonneg.mpr hZpos.le)
  -- Taylor's theorem
  have hTaylor : ∀ x : EuclideanSpace ℝ (Fin 4), ‖x‖ ≤ θ →
      |h x - h 0 - (fderiv ℝ h 0) x - (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ h) 0) x x|
        ≤ ((∫ y : EuclideanSpace ℝ (Fin 4), sKer y)⁻¹
            * ∫ u : EuclideanSpace ℝ (Fin 4), ‖iteratedFDeriv ℝ 3 (sKer (n := 4)) u‖)
          * θ ^ 3 :=
    fun x hx => Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_three_le
      (mul_nonneg (inv_nonneg.mpr hZpos.le) (integral_nonneg fun u => norm_nonneg _))
      (fun y hy => (hF_at3 y).congr_of_eventuallyEq (hident_ev y (by linarith)))
      (fun y hy => hbdd3 y (by linarith)) hx
  refine ⟨fderiv ℝ (fderiv ℝ h) 0, fderiv ℝ h 0, h 0, ?_, ?_⟩
  · rw [← laplacian_eq_sum_fderiv_fderiv (n := 4) (v := h) 0]
    exact hΔ 0 (Metric.mem_ball_self zero_lt_one)
  · intro x hx
    have hx' : ‖x‖ ≤ θ := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hx
    have h1 : |h x - (1 / 2 * (fderiv ℝ (fderiv ℝ h) 0) x x + (fderiv ℝ h 0) x + h 0)|
        = |h x - h 0 - (fderiv ℝ h 0) x
            - (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ h) 0) x x| := by
      congr 1
      ring
    rw [h1]
    exact (hTaylor x hx').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le 3))


end Commons.Analysis.Harmonic
