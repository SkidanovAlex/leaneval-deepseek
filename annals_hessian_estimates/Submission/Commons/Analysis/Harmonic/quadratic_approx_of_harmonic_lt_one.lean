import Mathlib
import Submission.Commons.Analysis.Harmonic.sphereAverage_harmonic_C2
import Submission.Commons.Analysis.Harmonic.radial_mollification_sphere_average
import Submission.Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_three_le
import Submission.Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball

/-!
# Quadratic approximation of a bounded harmonic function on a strictly smaller ball

We prove that a function `h` which is `C²`, harmonic and bounded by `1` on the unit ball of
`ℝⁿ` admits a quadratic approximation by a *trace-free* quadratic form `Q` (plus a linear form and
a constant) with error `O(θ³)` on the closed ball of radius `θ < 1`.

The proof is by mollification.  Choose a radial smooth kernel `ψ` vanishing outside the annulus
`R / 4 < ‖y‖ < R`, with `θ + 2R < 1` (the kernel must vanish near the origin so that its radial
profile, as a function of the real radius, is continuous and supported in `[0, R]`), and a smooth
cut-off `χ` which is `1` on `closedBall 0 (θ + 2R)` and supported in `ball 0 1`.  Putting `ht = χ * h`, the sphere mean value property of `h` implies that
`(ht ⋆ ψ) x = (∫ ψ) * h x` for every `x` with `‖x‖ ≤ θ + R`.  In particular `h` agrees on a
neighbourhood of the closed `θ`-ball with the smooth function `(∫ ψ)⁻¹ • (ht ⋆ ψ)`, and the
standard bound for the iterated derivatives of a convolution bounds `‖D^j h‖` for `j ≤ 3` by a
constant depending only on `ψ`.  Taylor's theorem with integral remainder then gives the claim.
-/

noncomputable section

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal ContDiff
  Convolution

namespace Commons.Analysis.Harmonic

set_option linter.style.haveILetI false

/-! ## The radial mollifying kernel and the cut-off -/

/-- The radius of the support of the mollifying kernel. -/
private def kerR (θ : ℝ) : ℝ := (1 - θ) / 4

/-- The scale of the mollifying kernel; `kerC θ * kerR θ = 4`. -/
private def kerC (θ : ℝ) : ℝ := 4 / kerR θ

/-- A smooth radial profile vanishing on `(-∞, 1]`, equal to `1` on `[2, 3]` and vanishing on
`[4, ∞)`. -/
private def kerProfile : ℝ → ℝ :=
  fun s => Real.smoothTransition (s - 1) * Real.smoothTransition (4 - s)

/-- The radius on which the cut-off equals `1`. -/
private def cutU (θ : ℝ) : ℝ := θ + 2 * kerR θ

/-- The scale of the cut-off. -/
private def cutB (θ : ℝ) : ℝ := 1 / (1 - cutU θ)

/-- A smooth radial kernel supported in the annulus `kerR θ / 4 < ‖y‖ < kerR θ`. -/
private def ker {n : ℕ} (θ : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  kerProfile (kerC θ * ‖y‖)

/-- A smooth cut-off equal to `1` on `closedBall 0 (cutU θ)` and vanishing outside `ball 0 1`. -/
private def cut {n : ℕ} (θ : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition (cutB θ - cutB θ * ‖y‖)

section Basic

variable {θ : ℝ}

private lemma kerR_pos (hθ1 : θ < 1) : 0 < kerR θ := by
  unfold kerR; linarith

private lemma kerC_pos (hθ1 : θ < 1) : 0 < kerC θ := by
  have := kerR_pos hθ1
  unfold kerC; positivity

private lemma kerC_mul_kerR (hθ1 : θ < 1) : kerC θ * kerR θ = 4 := by
  have h := (kerR_pos hθ1).ne'
  unfold kerC; field_simp

private lemma cutU_lt_one (hθ1 : θ < 1) : cutU θ < 1 := by
  unfold cutU kerR; linarith

private lemma cutU_pos (hθ : 0 < θ) : 0 < cutU θ := by
  unfold cutU kerR; linarith

private lemma cutB_pos (hθ1 : θ < 1) : 0 < cutB θ := by
  have h := cutU_lt_one hθ1
  unfold cutB; positivity

private lemma one_lt_cutB (hθ : 0 < θ) (hθ1 : θ < 1) : 1 < cutB θ := by
  have h := cutU_lt_one hθ1
  have h' := cutU_pos hθ
  unfold cutB
  rw [one_lt_div (by linarith)]
  linarith

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

private lemma kerProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) kerProfile := by
  unfold kerProfile
  fun_prop

private lemma kerProfile_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) : kerProfile t = 0 := by
  simp only [kerProfile, Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0),
    zero_mul]

private lemma kerProfile_eq_zero_of_ge_four {t : ℝ} (ht : 4 ≤ t) : kerProfile t = 0 := by
  simp only [kerProfile, Real.smoothTransition.zero_of_nonpos (by linarith : 4 - t ≤ 0),
    mul_zero]

private lemma kerProfile_ne_zero {t : ℝ} (h1 : 1 < t) (h2 : t < 4) : kerProfile t ≠ 0 := by
  refine mul_ne_zero (ne_of_gt (Real.smoothTransition.pos_of_pos (by linarith)))
    (ne_of_gt (Real.smoothTransition.pos_of_pos (by linarith)))

private lemma kerProfile_eq_one {t : ℝ} (h1 : 2 ≤ t) (h2 : t ≤ 3) : kerProfile t = 1 := by
  simp only [kerProfile, Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - 1),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 - t), mul_one]

/-! ## Properties of the mollifying kernel -/

section Kernel

variable {n : ℕ} {θ : ℝ}

private lemma ker_eq_zero_left (hθ1 : θ < 1) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ ≤ kerR θ / 4) : ker θ y = 0 := by
  refine kerProfile_eq_zero_of_le_one ?_
  have h1 : kerC θ * ‖y‖ ≤ kerC θ * (kerR θ / 4) :=
    mul_le_mul_of_nonneg_left hy (le_of_lt (kerC_pos hθ1))
  rw [← mul_div_assoc, kerC_mul_kerR hθ1] at h1
  linarith

private lemma ker_eq_zero (hθ1 : θ < 1) {y : EuclideanSpace ℝ (Fin n)}
    (hy : kerR θ ≤ ‖y‖) : ker θ y = 0 := by
  refine kerProfile_eq_zero_of_ge_four ?_
  have h1 : kerC θ * kerR θ ≤ kerC θ * ‖y‖ :=
    mul_le_mul_of_nonneg_left hy (le_of_lt (kerC_pos hθ1))
  rw [kerC_mul_kerR hθ1] at h1
  linarith

private lemma ker_contDiff (hθ1 : θ < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) => ker θ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n))
      (show (0 : ℝ) < kerR θ / 4 by linarith [kerR_pos hθ1])] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact ker_eq_zero_left hθ1 (le_of_lt hy)
  · have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => kerProfile (kerC θ * ‖y‖)) x := by
      have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => kerProfile (kerC θ * s)) ‖x‖ :=
        (kerProfile_contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt
      exact h3.comp x (contDiffAt_norm ℝ hx)
    simpa only [ker] using h2

private lemma ker_nonneg (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ ker θ y := by
  simp only [ker, kerProfile]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private lemma ker_le_one (y : EuclideanSpace ℝ (Fin n)) : ker θ y ≤ 1 := by
  simp only [ker, kerProfile]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

private lemma ker_even (y : EuclideanSpace ℝ (Fin n)) : ker θ (-y) = ker θ y := by
  simp only [ker, norm_neg]

private lemma ker_rad (_hθ1 : θ < 1) :
    ∀ (r : ℝ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1), 0 < r →
      ker θ (r • (v : EuclideanSpace ℝ (Fin n))) = kerProfile (kerC θ * r) := by
  intro r v hr
  simp only [ker, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp v.2, mul_one]

private lemma ker_tsupport (hθ1 : θ < 1) :
    tsupport (ker (n := n) θ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (kerR θ) := by
  intro y hy
  by_contra hcon
  rw [mem_closedBall, dist_zero_right, not_le] at hcon
  rw [tsupport, Metric.mem_closure_iff] at hy
  obtain ⟨z, hzs, hzd⟩ := hy ((‖y‖ - kerR θ) / 2) (by linarith)
  rw [Function.mem_support, ne_eq] at hzs
  rw [dist_eq_norm] at hzd
  have h1 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    have := norm_add_le (y - z) z
    rwa [sub_add_cancel] at this
  exact hzs (ker_eq_zero hθ1 (by linarith))

private lemma ker_hasCompactSupport (hθ1 : θ < 1) :
    HasCompactSupport (ker (n := n) θ) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (kerR θ)).of_isClosed_subset
    (isClosed_tsupport _) (ker_tsupport hθ1)

private lemma ker_eq_one (hθ1 : θ < 1) {y : EuclideanSpace ℝ (Fin n)}
    (hy1 : kerR θ / 2 ≤ ‖y‖) (hy2 : ‖y‖ ≤ 3 * kerR θ / 4) : ker θ y = 1 := by
  refine kerProfile_eq_one ?_ ?_
  · have h1 : kerC θ * (kerR θ / 2) ≤ kerC θ * ‖y‖ :=
      mul_le_mul_of_nonneg_left hy1 (le_of_lt (kerC_pos hθ1))
    rw [← mul_div_assoc, kerC_mul_kerR hθ1] at h1
    linarith
  · have h1 : kerC θ * ‖y‖ ≤ kerC θ * (3 * kerR θ / 4) :=
      mul_le_mul_of_nonneg_left hy2 (le_of_lt (kerC_pos hθ1))
    rw [show kerC θ * (3 * kerR θ / 4) = 3 * (kerC θ * kerR θ) / 4 by ring,
      kerC_mul_kerR hθ1] at h1
    linarith

private lemma ker_integral_pos (hn : 0 < n) (hθ1 : θ < 1) :
    0 < ∫ y : EuclideanSpace ℝ (Fin n), ker θ y := by
  have hρ : 0 < kerR θ / 8 := by linarith [kerR_pos hθ1]
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i0 1 with he
  have hen : ‖e‖ = 1 := by
    rw [he, PiLp.norm_single, norm_one]
  set y₀ : EuclideanSpace ℝ (Fin n) := (5 * kerR θ / 8) • e with hy0
  have hy0n : ‖y₀‖ = 5 * kerR θ / 8 := by
    rw [hy0, norm_smul, hen, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [kerR_pos hθ1])]
  have hone : ∀ z ∈ ball y₀ (kerR θ / 8), ker θ z = 1 := by
    intro z hz
    have hd : ‖z - y₀‖ < kerR θ / 8 := by
      rwa [mem_ball, dist_eq_norm] at hz
    refine ker_eq_one hθ1 ?_ ?_
    · have h4 : ‖y₀‖ ≤ ‖z - y₀‖ + ‖z‖ := by
        have := norm_add_le (y₀ - z) z
        rw [norm_sub_rev] at this
        rwa [sub_add_cancel] at this
      rw [hy0n] at h4
      linarith
    · have h4 : ‖z‖ ≤ ‖z - y₀‖ + ‖y₀‖ := by
        have := norm_add_le (z - y₀) y₀
        rwa [sub_add_cancel] at this
      rw [hy0n] at h4
      linarith
  have hker_int : Integrable (ker (n := n) θ) volume :=
    (ker_contDiff hθ1).continuous.integrable_of_hasCompactSupport (ker_hasCompactSupport hθ1)
  have hind_int : Integrable ((ball y₀ (kerR θ / 8)).indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_const measure_ball_ne_top (by simp)
  have hmono : (∫ y : EuclideanSpace ℝ (Fin n),
        (ball y₀ (kerR θ / 8)).indicator (fun _ => (1 : ℝ)) y)
      ≤ ∫ y : EuclideanSpace ℝ (Fin n), ker θ y := by
    refine integral_mono_ae hind_int hker_int (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ ball y₀ (kerR θ / 8)
    · rw [Set.indicator_of_mem hy, hone y hy]
    · rw [Set.indicator_of_notMem hy]
      exact ker_nonneg y
  have hval : (∫ y : EuclideanSpace ℝ (Fin n),
        (ball y₀ (kerR θ / 8)).indicator (fun _ => (1 : ℝ)) y)
      = volume.real (ball y₀ (kerR θ / 8)) := by
    rw [integral_indicator_const _ measurableSet_ball]
    simp
  rw [hval] at hmono
  have hpos : 0 < volume.real (ball y₀ (kerR θ / 8)) := by
    rw [MeasureTheory.Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos volume y₀ hρ).ne' measure_ball_ne_top
  linarith

end Kernel


/-! ## Properties of the cut-off -/

section Cutoff

variable {n : ℕ} {θ : ℝ}

private lemma cutB_mul (hθ1 : θ < 1) : cutB θ * (1 - cutU θ) = 1 := by
  have h := (cutU_lt_one hθ1).ne
  unfold cutB
  field_simp

private lemma cut_contDiff (hθ : 0 < θ) (hθ1 : θ < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) => cut θ y) :=
  contDiff_smoothTransition_sub_mul_norm (E := EuclideanSpace ℝ (Fin n))
    (c := cutB θ) (k := cutB θ) (cutB_pos hθ1) (one_lt_cutB hθ hθ1)

private lemma cut_nonneg (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ cut θ y :=
  Real.smoothTransition.nonneg _

private lemma cut_le_one (y : EuclideanSpace ℝ (Fin n)) : cut θ y ≤ 1 :=
  Real.smoothTransition.le_one _

private lemma cut_eq_one (_hθ : 0 < θ) (hθ1 : θ < 1) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ ≤ cutU θ) : cut θ y = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have h1 : cutB θ * (1 - cutU θ) ≤ cutB θ - cutB θ * ‖y‖ := by
    have h2 : cutB θ * (1 - cutU θ) ≤ cutB θ * (1 - ‖y‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (cutB_pos hθ1))
    linarith [mul_sub (cutB θ) 1 ‖y‖]
  rw [cutB_mul hθ1] at h1
  simpa only [cut] using h1

private lemma cut_eq_zero (hθ1 : θ < 1) {y : EuclideanSpace ℝ (Fin n)}
    (hy : 1 ≤ ‖y‖) : cut θ y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h1 : cutB θ - cutB θ * ‖y‖ ≤ 0 := by
    have h2 : cutB θ * ‖y‖ ≥ cutB θ * 1 := mul_le_mul_of_nonneg_left hy (le_of_lt (cutB_pos hθ1))
    linarith
  simpa only [cut] using h1

private lemma cut_support_subset (hθ1 : θ < 1) :
    Function.support (cut (n := n) θ) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  intro y hy
  rw [Function.mem_support] at hy
  rw [mem_ball, dist_zero_right]
  by_contra hcon
  rw [not_lt] at hcon
  exact hy (cut_eq_zero hθ1 hcon)

private lemma cut_hasCompactSupport (_hθ : 0 < θ) (hθ1 : θ < 1) :
    HasCompactSupport (cut (n := n) θ) := by
  have hsupp : tsupport (cut (n := n) θ) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [tsupport]
    exact closure_minimal (subset_trans (cut_support_subset hθ1) ball_subset_closedBall)
      isClosed_closedBall
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
    (isClosed_tsupport _) hsupp

end Cutoff

/-! ## The main theorem -/

theorem quadratic_approx_of_harmonic_lt_one {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 h (Metric.ball 0 1) →
      (∀ x ∈ Metric.ball 0 1, Laplacian.laplacian h x = 0) →
      (∀ x ∈ Metric.ball 0 1, |h x| ≤ 1) →
      ∃ (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (t : ℝ),
        (∑ i : Fin n, Q (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) ∧
        ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) θ,
          |h x - (1 / 2 * Q x x + q x + t)| ≤ C * θ ^ 3 := by
  have hRpos : 0 < kerR θ := kerR_pos hθ1
  have hθ2R : θ + 2 * kerR θ < 1 := by unfold kerR; linarith
  have hZpos : 0 < ∫ y : EuclideanSpace ℝ (Fin n), ker θ y := ker_integral_pos hn hθ1
  have hZne : (∫ y : EuclideanSpace ℝ (Fin n), ker θ y) ≠ 0 := ne_of_gt hZpos
  refine ⟨max ((∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹
      * ∫ u : EuclideanSpace ℝ (Fin n), ‖iteratedFDeriv ℝ 3 (ker (n := n) θ) u‖) 1,
    lt_max_of_lt_right zero_lt_one, ?_⟩
  intro h hh hΔ hb
  -- the truncated function
  let ht : EuclideanSpace ℝ (Fin n) → ℝ := fun y => cut θ y * h y
  have hcut_cont : Continuous (cut (n := n) θ) := (cut_contDiff hθ hθ1).continuous
  have ht_le_chi : ∀ y : EuclideanSpace ℝ (Fin n), ‖ht y‖ ≤ ‖cut θ y‖ := by
    intro y
    by_cases hy : cut θ y = 0
    · rw [show ht y = cut θ y * h y from rfl, hy, zero_mul]
    · have hyball : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        cut_support_subset hθ1 (Function.mem_support.mpr hy)
      have hyb : ‖h y‖ ≤ 1 := by
        rw [Real.norm_eq_abs]; exact hb y hyball
      rw [show ht y = cut θ y * h y from rfl, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hyb
  have ht_bound : ∀ y : EuclideanSpace ℝ (Fin n), ‖ht y‖ ≤ 1 := by
    intro y
    refine (ht_le_chi y).trans ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [cut_nonneg (θ := θ) y], cut_le_one (θ := θ) y⟩
  have ht_cont : Continuous ht := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx0 : cut θ x = 0
    · have hx0' : ht x = 0 := by
        rw [show ht x = cut θ x * h x from rfl, hx0, zero_mul]
      have hsq : Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ‖ht y‖) (𝓝 x) (𝓝 0) := by
        refine squeeze_zero (fun y => norm_nonneg _) (fun y => ht_le_chi y) ?_
        have h2 : Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ‖cut θ y‖) (𝓝 x)
            (𝓝 ‖cut θ x‖) := hcut_cont.norm.continuousAt
        rw [hx0, norm_zero] at h2
        exact h2
      have htend : Tendsto ht (𝓝 x) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsq
      change Tendsto ht (𝓝 x) (𝓝 (ht x))
      rw [hx0']
      exact htend
    · have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        cut_support_subset hθ1 (Function.mem_support.mpr hx0)
      have hcx : ContinuousAt h x := hh.continuousOn.continuousAt (isOpen_ball.mem_nhds hxball)
      exact hcut_cont.continuousAt.mul hcx
  have ht_cs : HasCompactSupport ht :=
    (cut_hasCompactSupport hθ hθ1).mul_right
  have ht_int : Integrable ht volume := ht_cont.integrable_of_hasCompactSupport ht_cs
  have ht_locint : LocallyIntegrable ht volume := ht_int.locallyIntegrable
  -- the mean value property of `h`
  have hMVP : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ r : ℝ, 0 < r →
      closedBall x r ⊆ ball 0 1 →
      (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          h (x + r • (v : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
        = (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            (1 : ℝ) ∂MeasureTheory.volume.toSphere) * h x := by
    intro x _ r hr hsub
    refine sphereAverage_harmonic_C2 hn hr (hh.mono ?_) (fun y hy => hΔ y ?_) ?_
    · exact subset_trans ball_subset_closedBall hsub
    · exact subset_trans ball_subset_closedBall hsub hy
    · exact (hh.mono hsub).continuousOn
  -- the radial profile of the kernel
  have hφcont : Continuous (fun r : ℝ => kerProfile (kerC θ * r)) :=
    kerProfile_contDiff.continuous.comp (continuous_const.mul continuous_id)
  have hφsupp : tsupport (fun r : ℝ => kerProfile (kerC θ * r)) ⊆ Icc 0 (kerR θ) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro r hr
    rw [Function.mem_support, ne_eq] at hr
    rw [mem_Icc]
    have hc : 0 < kerC θ := kerC_pos hθ1
    constructor
    · by_contra hcon
      rw [not_le] at hcon
      have h2 : kerC θ * r < 0 := mul_neg_of_pos_of_neg hc hcon
      exact hr (kerProfile_eq_zero_of_le_one (by linarith))
    · by_contra hcon
      rw [not_le] at hcon
      have h2 : kerC θ * kerR θ ≤ kerC θ * r := mul_le_mul_of_nonneg_left hcon.le hc.le
      rw [kerC_mul_kerR hθ1] at h2
      exact hr (kerProfile_eq_zero_of_ge_four h2)
  -- the mollification identity
  have hmoll : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ θ + kerR θ →
      (∫ y : EuclideanSpace ℝ (Fin n), h (x + y) * ker θ y)
        = (∫ y : EuclideanSpace ℝ (Fin n), ker θ y) * h x := by
    intro x hx
    refine radial_mollification_sphere_average hn hRpos hh.continuousOn hMVP
      (ker_contDiff hθ1).continuous (ker_tsupport hθ1) hφcont hφsupp (ker_rad hθ1) ?_
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_zero_right]
    calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
          have h1 := norm_add_le (y - x) x
          rwa [sub_add_cancel] at h1
      _ ≤ kerR θ + (θ + kerR θ) := add_le_add hy hx
      _ < 1 := by linarith
  -- the identification of `h` with a convolution
  let G : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ker θ)) x
  let F : EuclideanSpace ℝ (Fin n) → ℝ := (∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹ • G
  have hconv : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ θ + kerR θ → h x = F x := by
    intro x hx
    have hA : (∫ t : EuclideanSpace ℝ (Fin n), ht t * ker θ (x - t))
        = ∫ t : EuclideanSpace ℝ (Fin n), ht (x - t) * ker θ t := by
      have h1 := integral_sub_left_eq_self
        (fun u : EuclideanSpace ℝ (Fin n) => ht (x - u) * ker θ u) volume x
      rwa [show (fun u : EuclideanSpace ℝ (Fin n) => ht (x - (x - u)) * ker θ (x - u))
          = (fun u : EuclideanSpace ℝ (Fin n) => ht u * ker θ (x - u)) from by
            funext u; rw [show x - (x - u) = u from by abel]] at h1
    have hB : (∫ t : EuclideanSpace ℝ (Fin n), ht (x - t) * ker θ t)
        = ∫ t : EuclideanSpace ℝ (Fin n), h (x - t) * ker θ t := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [show ht (x - t) = cut θ (x - t) * h (x - t) from rfl]
      by_cases hk : ker θ t = 0
      · rw [hk, mul_zero, mul_zero]
      · have htmem : t ∈ tsupport (ker (n := n) θ) :=
          subset_tsupport _ (Function.mem_support.mpr hk)
        have htnorm : ‖t‖ ≤ kerR θ := by
          have h1 := ker_tsupport hθ1 htmem
          rwa [mem_closedBall, dist_zero_right] at h1
        have hcut1 : cut θ (x - t) = 1 := by
          refine cut_eq_one hθ hθ1 ?_
          calc ‖x - t‖ ≤ ‖x‖ + ‖t‖ := norm_sub_le x t
            _ ≤ (θ + kerR θ) + kerR θ := add_le_add hx htnorm
            _ = cutU θ := by unfold cutU; ring
        rw [hcut1, one_mul]
    have hC : (∫ t : EuclideanSpace ℝ (Fin n), h (x - t) * ker θ t)
        = ∫ t : EuclideanSpace ℝ (Fin n), h (x + t) * ker θ t := by
      have h0 := integral_neg_eq_self
        (fun u : EuclideanSpace ℝ (Fin n) => h (x + u) * ker θ u) volume
      have h1 : (∫ u : EuclideanSpace ℝ (Fin n), h (x - u) * ker θ u)
          = ∫ u : EuclideanSpace ℝ (Fin n), h (x + -u) * ker θ (-u) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show h (x - u) * ker θ u = h (x + -u) * ker θ (-u)
        rw [show x - u = x + -u from sub_eq_add_neg x u, ker_even]
      rw [h1, h0]
    have hstep : G x = (∫ y : EuclideanSpace ℝ (Fin n), ker θ y) * h x := by
      show (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ker θ)) x = _
      rw [MeasureTheory.convolution_lsmul]
      simp only [smul_eq_mul]
      rw [hA, hB, hC, hmoll x hx]
    show h x = F x
    change h x = (∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹ * G x
    rw [hstep, ← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
  -- smoothness of `F`
  have hS : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ker θ)) x) :=
    (ker_hasCompactSupport hθ1).contDiff_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) ht_locint (ker_contDiff hθ1)
  have hF_cd : ContDiff ℝ (⊤ : ℕ∞) F :=
    hS.const_smul ((∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹)
  have hF_at3 : ∀ x : EuclideanSpace ℝ (Fin n), ContDiffAt ℝ 3 F x :=
    fun x => (hF_cd.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hident_ev : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ θ → h =ᶠ[𝓝 x] F := by
    intro x hx
    have hε : 0 < θ + kerR θ - ‖x‖ := by linarith
    filter_upwards [Metric.closedBall_mem_nhds x hε] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hy' : ‖y‖ ≤ θ + kerR θ := by
      calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            have h1 := norm_add_le (y - x) x
            rwa [sub_add_cancel] at h1
        _ ≤ (θ + kerR θ - ‖x‖) + ‖x‖ := add_le_add hy le_rfl
        _ = θ + kerR θ := by ring
    exact hconv y hy'
  -- the third derivative bound
  have hiter_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ 3 (ker (n := n) θ) y) volume :=
    ((ker_contDiff hθ1).continuous_iteratedFDeriv (m := 3)
      (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      ((ker_hasCompactSupport hθ1).iteratedFDeriv (𝕜 := ℝ) 3)
  have hbdd3 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ θ →
      ‖iteratedFDeriv ℝ 3 h x‖
        ≤ (∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹
          * ∫ u : EuclideanSpace ℝ (Fin n), ‖iteratedFDeriv ℝ 3 (ker (n := n) θ) u‖ := by
    intro x hx
    have hieq : iteratedFDeriv ℝ 3 h x = iteratedFDeriv ℝ 3 F x :=
      ((hident_ev x hx).iteratedFDeriv ℝ 3).eq_of_nhds
    rw [hieq]
    have hsmul : iteratedFDeriv ℝ 3 F x
        = (∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹ •
            iteratedFDeriv ℝ 3 G x := by
      have h1 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := 3)
        (a := (∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹) (f := G) (x := x)
        ((hS.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top))
      simpa only [F] using h1
    rw [hsmul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hZpos.le)]
    have h2 : iteratedFDeriv ℝ 3 G x = (ht ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => iteratedFDeriv ℝ 3 (ker (n := n) θ) y)) x :=
      congrFun (Commons.Analysis.Calculus.BumpFunction.iteratedFDeriv_convolution_lsmul (μ := volume) (f := ht) (g := ker (n := n) θ)
        ht_locint (ker_contDiff hθ1) (ker_hasCompactSupport hθ1) 3) x
    rw [h2]
    exact mul_le_mul_of_nonneg_left
      (Commons.Analysis.Calculus.BumpFunction.norm_convolution_lsmul_le_integral (μ := volume) ht_bound hiter_int x)
      (inv_nonneg.mpr hZpos.le)
  -- Taylor's theorem
  have hTaylor : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ θ →
      |h x - h 0 - (fderiv ℝ h 0) x - (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ h) 0) x x|
        ≤ ((∫ y : EuclideanSpace ℝ (Fin n), ker θ y)⁻¹
            * ∫ u : EuclideanSpace ℝ (Fin n), ‖iteratedFDeriv ℝ 3 (ker (n := n) θ) u‖)
          * θ ^ 3 :=
    fun x hx => Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_three_le
      (mul_nonneg (inv_nonneg.mpr hZpos.le) (integral_nonneg fun u => norm_nonneg _))
      (fun y hy => (hF_at3 y).congr_of_eventuallyEq (hident_ev y hy))
      (fun y hy => hbdd3 y hy) hx
  refine ⟨fderiv ℝ (fderiv ℝ h) 0, fderiv ℝ h 0, h 0, ?_, ?_⟩
  · rw [← laplacian_eq_sum_fderiv_fderiv (n := n) (v := h) 0]
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
