import Mathlib
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Commons.Analysis.Complex.divisor_sum_le_circleAverage
import Submission.Commons.Analysis.Complex.Cartan.monic_level_set_volume_le
import Submission.Commons.Analysis.Complex.kovrijkine_ratio
import Submission.Commons.Measure.EuclideanSpace.exists_segment_large_intersection
import Submission.Commons.Analysis.Complex.Harmonic.harnack_inequality_ball

open MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Commons.Analysis.Complex

open Polynomial

section helpers

/-- Algebraic identity underlying the Blaschke factor. -/
private lemma normSq_blaschke_identity {r : ℝ} (u z : ℂ) :
    Complex.normSq ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)
      - (r ^ 2) * Complex.normSq (z - u)
      = (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow]
  ring

/-- The Blaschke denominator does not vanish on the closed disk when `‖u‖ < r`. -/
private lemma blaschke_denom_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r)
    (hz : ‖z‖ ≤ r) : (r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 := by
  have hr2 : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  have hbound : ‖(starRingEnd ℂ) u * z‖ < ‖(r : ℂ) ^ 2‖ := by
    rw [norm_mul, show ‖(starRingEnd ℂ) u‖ = ‖u‖ by simp, hr2]
    nlinarith [norm_nonneg u, norm_nonneg z, hu, hz]
  intro h
  have hzero : ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ = 0 := by rw [h, norm_zero]
  have htri : ‖(r : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) u * z‖
      ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
    le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
  linarith [hbound]

/-- The Blaschke factor is bounded by `1` on the closed disk. -/
private lemma blaschke_norm_le_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ ≤ r)
    (hz : ‖z‖ ≤ r) :
    ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ≤ 1 := by
  have hsq : (r * ‖z - u‖) ^ 2 ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    have hid := normSq_blaschke_identity (r := r) u z
    have hnn : 0 ≤ (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
      apply mul_nonneg <;> rw [Complex.normSq_eq_norm_sq] <;>
        nlinarith [norm_nonneg z, norm_nonneg u, hu, hz]
    linarith [hid]
  have hle : r * ‖z - u‖ ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at h
  rcases eq_or_ne ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) 0 with h | h
  · rw [h, div_zero, norm_zero]; norm_num
  · rw [norm_div, norm_mul, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr],
      div_le_one (norm_pos_iff.mpr h)]
    exact hle

/-- The Blaschke factor has modulus exactly `1` on the boundary circle. -/
private lemma blaschke_norm_eq_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r)
    (hz : ‖z‖ = r) :
    ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ = 1 := by
  have hden := blaschke_denom_aux hr hu hz.le
  have hsq : (r * ‖z - u‖) ^ 2 = ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    have hid := normSq_blaschke_identity (r := r) u z
    have hz2 : Complex.normSq z = r ^ 2 := by rw [Complex.normSq_eq_norm_sq, hz]
    rw [hz2, sub_self, zero_mul] at hid
    linarith [hid]
  have habs : |r * ‖z - u‖| = |‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at habs
  rw [norm_div, norm_mul, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  rw [div_eq_one_iff_eq (ne_of_gt (norm_pos_iff.mpr hden))]
  exact habs

/-- Circle average of `log ‖φ‖` at radius `3` is bounded by `log M` when `‖φ‖ ≤ M` on `ball 0 3`. -/
private theorem circleAverage_log_norm_le_log_of_bound_three {φ : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 5))
    (hb : ∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖φ z‖ ≤ M) :
    Real.circleAverage (fun z : ℂ => Real.log ‖φ z‖) 0 3 ≤ Real.log M := by
  have hcl3 : closure (Metric.ball (0:ℂ) (3:ℝ)) = Metric.closedBall 0 3 :=
    closure_ball 0 (by norm_num)
  have hcont : ContinuousOn (fun z : ℂ => ‖φ z‖) (closure (Metric.ball (0:ℂ) (3:ℝ))) := by
    rw [hcl3]
    exact (hφ.mono (Metric.closedBall_subset_ball (by norm_num))).continuousOn.norm
  have himg : ((fun z : ℂ => ‖φ z‖) '' Metric.ball (0:ℂ) (3:ℝ)) ⊆ Set.Iic M := by
    rintro y ⟨z, hz, rfl⟩
    exact hb z hz
  have hclosed : ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖φ z‖ ≤ M := by
    intro z hz
    rw [← hcl3] at hz
    exact closure_minimal himg isClosed_Iic (hcont.image_closure (s := Metric.ball (0:ℂ) 3) ⟨z, hz, rfl⟩)
  have hint : CircleIntegrable (fun z : ℂ => Real.log ‖φ z‖) 0 3 :=
    (hφ.mono (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by norm_num)))).meromorphicOn.circleIntegrable_log_norm
  refine Real.circleAverage_mono_on_of_le_circle hint (fun z hz => ?_)
  rw [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] at hz
  rcases eq_or_ne (φ z) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM
  · exact Real.log_le_log (norm_pos_iff.mpr h0)
      (hclosed z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.le))

end helpers

/-- Harnack lower bound: a zero-free analytic function on `ball 0 2`, bounded by `M`, with
`1 ≤ ‖h 0‖`, is bounded below by `M^{-4}` on `[-1,1]`. -/
private theorem harnack_lower_bound_two (h : ℂ → ℂ) (M : ℝ) (hM : 1 ≤ M)
    (han : AnalyticOnNhd ℂ h (Metric.ball 0 2))
    (hne : ∀ z ∈ Metric.ball 0 2, h z ≠ 0)
    (hMbd : ∀ z ∈ Metric.ball 0 2, ‖h z‖ ≤ M)
    (h0 : 1 ≤ ‖h 0‖) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → (M^4)⁻¹ ≤ ‖h x‖ := by
  intro x hx
  have hxabs1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
  have hxnorm : ‖(x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hxabs1
  set g : ℂ → ℂ := fun z => (M : ℂ) / h z with hg_def
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hgan : AnalyticOnNhd ℂ g (Metric.ball 0 2) := by
    rw [hg_def]
    exact (analyticOnNhd_const).div han (fun z hz => hne z hz)
  have hgne : ∀ z ∈ Metric.ball 0 2, g z ≠ 0 := by
    intro z hz
    rw [hg_def]
    exact div_ne_zero (by exact_mod_cast ne_of_gt hMpos) (hne z hz)
  have hgnorm : ∀ z : ℂ, ‖g z‖ = M / ‖h z‖ := by
    intro z
    rw [hg_def, norm_div, Complex.norm_of_nonneg hMpos.le]
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖g z‖)
      (Metric.closedBall 0 ((3:ℝ)/2)) := by
    intro z hz
    have hz2 : z ∈ Metric.ball 0 2 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith
    exact (hgan z hz2).harmonicAt_log_norm (hgne z hz2)
  have hpos : ∀ z ∈ Metric.closedBall 0 ((3:ℝ)/2), 0 ≤ Real.log ‖g z‖ := by
    intro z hz
    have hz2 : z ∈ Metric.ball 0 2 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith
    rw [hgnorm]
    apply Real.log_nonneg
    rw [le_div_iff₀ (norm_pos_iff.mpr (hne z hz2))]
    linarith [hMbd z hz2]
  have hxball : (x : ℂ) ∈ Metric.ball (0:ℂ) ((3:ℝ)/2) := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  obtain ⟨_, hub⟩ :=
    Harmonic.harnack_inequality_ball (a := (0:ℂ)) (R := ((3:ℝ)/2)) hharm hpos hxball
  simp only [sub_zero] at hub
  have hfac : (((3:ℝ)/2) + ‖(x:ℂ)‖) / (((3:ℝ)/2) - ‖(x:ℂ)‖) ≤ 5 := by
    have hden : 0 < ((3:ℝ)/2) - ‖(x:ℂ)‖ := by linarith [norm_nonneg (x:ℂ)]
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg (x:ℂ), hxnorm]
  have h0pos : 0 < ‖h 0‖ := norm_pos_iff.mpr (by intro hc; rw [hc, norm_zero] at h0; linarith)
  have hf0 : Real.log ‖g 0‖ ≤ Real.log M := by
    rw [hgnorm]
    apply Real.log_le_log (div_pos hMpos h0pos)
    rw [div_le_iff₀ h0pos]; nlinarith [h0, hMpos]
  have hfx : Real.log ‖g x‖ ≤ 5 * Real.log M := by
    have h2 : (((3:ℝ)/2) + ‖(x:ℂ)‖) / (((3:ℝ)/2) - ‖(x:ℂ)‖) * Real.log ‖g 0‖
        ≤ 5 * Real.log M :=
      mul_le_mul hfac hf0 (hpos 0 (by rw [Metric.mem_closedBall, dist_self]; norm_num)) (by norm_num)
    linarith
  have hxr : (x:ℂ) ∈ Metric.ball 0 2 := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hhxne : h x ≠ 0 := hne (x:ℂ) hxr
  have hhxpos : 0 < ‖h x‖ := norm_pos_iff.mpr hhxne
  have hlogx : Real.log ‖g x‖ = Real.log M - Real.log ‖h x‖ := by
    rw [hgnorm, Real.log_div (ne_of_gt hMpos) (ne_of_gt hhxpos)]
  rw [hlogx] at hfx
  have hfin : -4 * Real.log M ≤ Real.log ‖h x‖ := by linarith
  have hexp : Real.exp (-4 * Real.log M) ≤ Real.exp (Real.log ‖h x‖) := Real.exp_le_exp.mpr hfin
  rw [Real.exp_log hhxpos] at hexp
  have hexp2 : Real.exp (4 * Real.log M) = M^4 := by
    have h : (4:ℝ) * Real.log M = Real.log (M^4) := by rw [Real.log_pow]; norm_num
    rw [h, Real.exp_log (by positivity)]
  have hgoal : Real.exp (-4 * Real.log M) = (M^4)⁻¹ := by
    rw [show -4 * Real.log M = -(4 * Real.log M) by ring, Real.exp_neg, hexp2]
  rwa [hgoal] at hexp

/-- Arithmetic: absorb the factor `M^5` and the base `100` into `(10^6 / v) ^ (10^6 log M)`. -/
private lemma ratio_absorb {v M a : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) (hM1 : 1 ≤ M) (ha : 0 ≤ a) :
    (100 / v) ^ (10 * Real.log M) * M^5 * a ≤ (10^6 / v) ^ (10^6 * Real.log M) * a := by
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hv100 : (0:ℝ) < 100 / v := by positivity
  have hv6 : (0:ℝ) < (10:ℝ)^6 / v := by positivity
  have hv61 : (1:ℝ) ≤ (10:ℝ)^6 / v := by rw [le_div_iff₀ hv0]; nlinarith [hv1]
  have hlog10 : (5:ℝ) ≤ Real.log ((10:ℝ)^6) := by
    rw [← Real.log_exp 5]
    apply Real.log_le_log (Real.exp_pos 5)
    have h2 : (Real.exp 1)^5 ≤ (3:ℝ)^5 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5
    rw [show (5:ℝ) = (5:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    norm_num at h2 ⊢
    linarith
  have hstep1 : M^5 ≤ ((10:ℝ)^6) ^ (Real.log M) := by
    calc M^5 = M ^ (5:ℝ) := (Real.rpow_natCast M 5).symm
      _ ≤ M ^ (Real.log ((10:ℝ)^6)) := Real.rpow_le_rpow_of_exponent_le hM1 hlog10
      _ = ((10:ℝ)^6) ^ (Real.log M) := by
          rw [Real.rpow_def_of_pos hM0, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 10^6)]
          congr 1; ring
  have hstep2 : (100 / v) ^ (10 * Real.log M) ≤ ((10:ℝ)^6 / v) ^ (10 * Real.log M) :=
    Real.rpow_le_rpow (le_of_lt hv100) (by
      rw [div_le_div_iff_of_pos_right hv0]; norm_num) (mul_nonneg (by norm_num) hlogM)
  have hA : ((10:ℝ)^6) ^ (Real.log M) ≤ ((10:ℝ)^6 / v) ^ (Real.log M) :=
    Real.rpow_le_rpow (by norm_num) (by rw [le_div_iff₀ hv0]; nlinarith [hv1]) hlogM
  have hexp_le : Real.log M ≤ ((10:ℝ)^6 - 10) * Real.log M := by
    have h : (1:ℝ) ≤ (10:ℝ)^6 - 10 := by norm_num
    calc Real.log M = 1 * Real.log M := (one_mul _).symm
      _ ≤ ((10:ℝ)^6 - 10) * Real.log M := mul_le_mul_of_nonneg_right h hlogM
  have hB : ((10:ℝ)^6 / v) ^ (Real.log M) ≤ ((10:ℝ)^6 / v) ^ (((10:ℝ)^6 - 10) * Real.log M) :=
    Real.rpow_le_rpow_of_exponent_le hv61 hexp_le
  have hsplit : ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M)
      = ((10:ℝ)^6 / v) ^ (10 * Real.log M) * ((10:ℝ)^6 / v) ^ (((10:ℝ)^6 - 10) * Real.log M) := by
    rw [← Real.rpow_add hv6]
    congr 1
    ring
  have hstep3 : ((10:ℝ)^6) ^ (Real.log M) * ((10:ℝ)^6 / v) ^ (10 * Real.log M)
      ≤ ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M) := by
    rw [hsplit]
    calc ((10:ℝ)^6) ^ (Real.log M) * ((10:ℝ)^6 / v) ^ (10 * Real.log M)
        ≤ ((10:ℝ)^6 / v) ^ (Real.log M) * ((10:ℝ)^6 / v) ^ (10 * Real.log M) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = ((10:ℝ)^6 / v) ^ (10 * Real.log M) * ((10:ℝ)^6 / v) ^ (Real.log M) := by ring
      _ ≤ ((10:ℝ)^6 / v) ^ (10 * Real.log M) * ((10:ℝ)^6 / v) ^ (((10:ℝ)^6 - 10) * Real.log M) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  have hmain : (100 / v) ^ (10 * Real.log M) * M^5 ≤ ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M) := by
    calc (100 / v) ^ (10 * Real.log M) * M^5 = M^5 * ((100 / v) ^ (10 * Real.log M)) := by ring
      _ ≤ ((10:ℝ)^6) ^ (Real.log M) * ((100 / v) ^ (10 * Real.log M)) :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ ≤ ((10:ℝ)^6) ^ (Real.log M) * (((10:ℝ)^6 / v) ^ (10 * Real.log M)) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ ≤ ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M) := hstep3
  calc (100 / v) ^ (10 * Real.log M) * M^5 * a
      = ((100 / v) ^ (10 * Real.log M) * M^5) * a := by ring
    _ ≤ ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M) * a := mul_le_mul_of_nonneg_right hmain ha

/-- **Blaschke/Cartan core, radius `2`/bound on disk `3`.**
For `φ` analytic on `ball 0 5`, bounded by `M` on `ball 0 3`, with `1 ≤ ‖φ 0‖`, one can factor out
the zeros of `φ` in `ball 0 2` as a finite Blaschke product `b` times a zero-free `h`, and the
resulting polynomial `P` has degree `N` with `N log (3/2) ≤ log M`. -/
private theorem kovrijkine_blaschke_core_three (φ : ℂ → ℂ) (M : ℝ)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 5))
    (hbound : ∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖φ z‖ ≤ M)
    (hM1 : 1 ≤ M) (hφ0 : 1 ≤ ‖φ 0‖) :
    ∃ (N : ℕ) (b h : ℂ → ℂ) (P : Polynomial ℂ),
      P.Monic ∧ P.natDegree = N ∧
      AnalyticOnNhd ℂ b (Metric.ball 0 2) ∧ AnalyticOnNhd ℂ h (Metric.ball 0 2) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 2 → h z ≠ 0) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 2 → φ z = b z * h z) ∧
      (∀ z : ℂ, ‖z‖ = 2 → ‖b z‖ = 1) ∧ (∀ z : ℂ, z ∈ Metric.ball 0 2 → ‖b z‖ ≤ 1) ∧
      (∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → ‖P.eval (x:ℂ)‖ ≤ (3:ℝ) ^ N * ‖b (x:ℂ)‖) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 2 → ‖h z‖ ≤ M) ∧ 1 ≤ ‖h 0‖ ∧
      (N : ℝ) * Real.log (3 / 2) ≤ Real.log M := by
  classical
  set r : ℝ := 2 with hr_def
  have hr : (0:ℝ) < r := by rw [hr_def]; norm_num
  have hr5 : r < 5 := by rw [hr_def]; norm_num
  have hr3 : r < 3 := by rw [hr_def]; norm_num
  have hr1 : (1:ℝ) < r := by rw [hr_def]; norm_num
  have hφ0ne : φ 0 ≠ 0 := by intro h; rw [h, norm_zero] at hφ0; linarith
  -- (1) divisor support finite on ball 0 r
  have h3 : (MeromorphicOn.divisor φ (Metric.ball 0 r)).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite ((hφ.mono (Metric.closedBall_subset_ball hr5)).meromorphicOn)
  -- (2) all orders are finite on ball 0 5
  have h0mem5 : (0:ℂ) ∈ Metric.ball 0 (5:ℝ) := by rw [Metric.mem_ball, dist_zero_right]; norm_num
  have h2 : ∀ z ∈ Metric.ball 0 (5:ℝ), meromorphicOrderAt φ z ≠ ⊤ := by
    have hconn : IsConnected (Metric.ball (0:ℂ) (5:ℝ)) := Metric.isConnected_ball (by norm_num : (0:ℝ) < 5)
    have hex := (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hφ.meromorphicOn hconn)
    intro z hz
    refine (hex.1 ⟨⟨0, h0mem5⟩, ?_⟩) ⟨z, hz⟩
    exact meromorphicOrderAt_ne_top_of_analytic_ne_zero (hφ 0 h0mem5) hφ0ne
  -- (3) factor out the zeros
  obtain ⟨g, hg_an, hg_nz, hg_eq⟩ :=
    factor_subBall_divisor (U := Metric.ball 0 (5:ℝ)) (V := Metric.ball 0 r)
      (Metric.ball_subset_ball (le_of_lt hr5)) hφ.meromorphicOn h2 hφ h3
  -- notation
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor φ (Metric.ball 0 r) u
  let S : Finset ℂ := h3.toFinset
  have hS_coe : (S : Set ℂ) = Function.support D := by
    simpa [S, D, Function.support] using h3.coe_toFinset
  let dn : ℂ → ℕ := fun u => (D u).toNat
  let N : ℕ := ∑ u ∈ S, dn u
  let P : Polynomial ℂ := ∏ u ∈ S, (X - C u) ^ dn u
  let Qf : ℂ → ℂ := fun z => ∏ u ∈ S, ((r:ℂ)^2 - (starRingEnd ℂ) u * z) ^ dn u
  let b : ℂ → ℂ := fun z => ∏ u ∈ S,
    ((r:ℂ) * (z - u) / ((r:ℂ)^2 - (starRingEnd ℂ) u * z)) ^ dn u
  let h : ℂ → ℂ := fun z => g z * Qf z / (r:ℂ)^N
  -- membership facts
  have hD_mem : ∀ u, D u ≠ 0 → u ∈ Metric.ball 0 r := by
    intro u hu
    by_contra hc
    apply hu
    show MeromorphicOn.divisor φ (Metric.ball 0 r) u = 0
    rw [MeromorphicOn.divisor_def]
    simp [hc]
  have hS_lt : ∀ u ∈ S, ‖u‖ < r := by
    intro u hu
    have hu' : u ∈ Function.support D := by rw [← hS_coe]; exact hu
    rw [Function.mem_support] at hu'
    have := hD_mem u hu'
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hD_nonneg : ∀ u, 0 ≤ D u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hφ.mono (Metric.ball_subset_ball (le_of_lt hr5))) u
  have hQf_ne : ∀ z, ‖z‖ ≤ r → Qf z ≠ 0 := by
    intro z hz
    change (∏ u ∈ S, ((r:ℂ)^2 - (starRingEnd ℂ) u * z) ^ (dn u)) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    exact pow_ne_zero _ (blaschke_denom_aux hr (hS_lt u hu) hz)
  -- P.eval identity
  have hPz : ∀ z : ℂ, (∏ᶠ u : ℂ, (z - u) ^ (D u)) = P.eval z := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (D u)) ?_]
    · have hstep : ∀ u ∈ S, (z - u) ^ (D u) = (z - u) ^ (dn u) := by
        intro u hu
        have hdu : D u = (dn u : ℤ) := by
          show D u = ((D u).toNat : ℤ)
          exact (Int.toNat_of_nonneg (hD_nonneg u)).symm
        rw [hdu, zpow_natCast]
      rw [Finset.prod_congr rfl hstep]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [hS_coe, Function.mem_support]
      intro hD0
      exact hu (by rw [hD0, zpow_zero])
  -- phi = P.eval * g on ball 0 5
  have hφ_Pg : ∀ z ∈ Metric.ball 0 (5:ℝ), φ z = P.eval z * g z := by
    intro z hz
    rw [← hPz z]
    exact hg_eq z hz
  have hr2norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  -- explicit eval of P
  have hPeval : ∀ z : ℂ, P.eval z = ∏ u ∈ S, (z - u) ^ (dn u) := by
    intro z
    dsimp only [P]
    simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  have hPmonic : P.Monic := by
    dsimp only [P]
    exact Polynomial.monic_prod_of_monic S _ (fun u hu => (Polynomial.monic_X_sub_C u).pow _)
  have hPdeg : P.natDegree = N := by
    dsimp only [P, N]
    rw [Polynomial.natDegree_prod S _ (fun u hu => pow_ne_zero _ (Polynomial.monic_X_sub_C u).ne_zero)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  -- b as quotient
  have hb_eq : ∀ z : ℂ, Qf z ≠ 0 → b z = (r : ℂ) ^ N * P.eval z / Qf z := by
    intro z hQz
    dsimp only [b, Qf]
    simp only [div_pow]
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [Finset.prod_congr rfl (fun u hu => mul_pow (r : ℂ) (z - u) (dn u)),
        Finset.prod_mul_distrib, hPeval z, Finset.prod_pow_eq_pow_sum]
  -- analyticity
  have hb_an : AnalyticOnNhd ℂ b (Metric.ball 0 r) := by
    dsimp only [b]
    have key := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := Metric.ball 0 r)
      (f := fun u z => ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) S
      (fun u hu => by
        refine AnalyticOnNhd.pow ?_ (dn u)
        refine AnalyticOnNhd.div ?_ ?_ ?_
        · exact analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)
        · exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
        · intro z hz
          rw [Metric.mem_ball, dist_zero_right] at hz
          exact blaschke_denom_aux hr (hS_lt u hu) (le_of_lt hz))
    rw [show (∏ n ∈ S, (fun u z =>
          ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) n)
        = (fun z => ∏ u ∈ S,
          ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) from
      by funext z; rw [Finset.prod_apply]] at key
    exact key
  have hQf_an5 : AnalyticOnNhd ℂ Qf (Metric.ball 0 (5:ℝ)) := by
    dsimp only [Qf]
    have key := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := Metric.ball 0 (5:ℝ))
      (f := fun u z => ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) S
      (fun u hu => AnalyticOnNhd.pow
        (analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)) (dn u))
    rw [show (∏ n ∈ S, (fun u z => ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) n)
        = (fun z => ∏ u ∈ S, ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) from
      by funext z; rw [Finset.prod_apply]] at key
    exact key
  have hQf_an : AnalyticOnNhd ℂ Qf (Metric.ball 0 r) :=
    hQf_an5.mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hrc_ne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hh_an5 : AnalyticOnNhd ℂ h (Metric.ball 0 (5:ℝ)) := by
    dsimp only [h]
    exact (hg_an.mul hQf_an5).div analyticOnNhd_const (fun z hz => pow_ne_zero _ hrc_ne)
  have hh_an : AnalyticOnNhd ℂ h (Metric.ball 0 r) :=
    hh_an5.mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hh_ne : ∀ z ∈ Metric.ball 0 r, h z ≠ 0 := by
    intro z hz
    have hzr : ‖z‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    dsimp only [h]
    exact div_ne_zero (mul_ne_zero (hg_nz z hz) (hQf_ne z hzr)) (pow_ne_zero _ hrc_ne)
  -- phi = b * h on the closed ball
  have hφ_eq_bh_cl : ∀ z ∈ Metric.closedBall 0 r, φ z = b z * h z := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hz5 : z ∈ Metric.ball 0 (5:ℝ) := Metric.closedBall_subset_ball hr5 hz
    have hQz := hQf_ne z hzr
    rw [hφ_Pg z hz5, hb_eq z hQz]
    dsimp only [h]
    field_simp
  -- boundary and disk values of b
  have hb_circ : ∀ z : ℂ, ‖z‖ = r → ‖b z‖ = 1 := by
    intro z hz
    dsimp only [b]
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro u hu
    rw [norm_pow, blaschke_norm_eq_aux hr (hS_lt u hu) hz, one_pow]
  have hb_le1 : ∀ z ∈ Metric.ball 0 r, ‖b z‖ ≤ 1 := by
    intro z hz
    have hzr : ‖z‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    dsimp only [b]
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro u hu
      positivity
    · intro u hu
      calc ‖((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u‖
          = ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ^ dn u := norm_pow _ _
        _ ≤ 1 ^ dn u :=
            pow_le_pow_left₀ (norm_nonneg _) (blaschke_norm_le_aux hr (hS_lt u hu).le hzr) (dn u)
        _ = 1 := one_pow _
  -- polynomial inequality
  have hpoly : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 →
      ‖P.eval (x:ℂ)‖ ≤ (r+1)^N * ‖b (x:ℂ)‖ := by
    intro x hx
    have hxnn : 0 ≤ x := hx.1
    have hxle1 : x ≤ 1 := hx.2
    have hxr : ‖(x:ℂ)‖ ≤ r := by
      rw [show ‖(x:ℂ)‖ = |x| by simp, abs_of_nonneg hxnn]; linarith [hr1]
    have hxs : ‖(x:ℂ)‖ ≤ 1 := by
      rw [show ‖(x:ℂ)‖ = |x| by simp, abs_of_nonneg hxnn]; exact hxle1
    have hPx : ‖P.eval (x:ℂ)‖ = ∏ u ∈ S, ‖(x:ℂ) - u‖ ^ dn u := by
      rw [hPeval, norm_prod]
      simp [norm_pow]
    have hbx : ‖b (x:ℂ)‖ = ∏ u ∈ S,
        ‖(r:ℂ) * ((x:ℂ) - u) / ((r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ))‖ ^ dn u := by
      dsimp only [b]
      rw [norm_prod]
      simp [norm_pow]
    rw [hPx, hbx, ← Finset.prod_pow_eq_pow_sum S dn (r+1), ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro u hu; positivity
    · intro u hu
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hden := blaschke_denom_aux hr (hS_lt u hu) hxr
      have hdpos : 0 < ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖ := norm_pos_iff.mpr hden
      have hdle : ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖ ≤ (r+1) * r := by
        have h1 : ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖
            ≤ ‖(r:ℂ)^2‖ + ‖(starRingEnd ℂ) u * (x:ℂ)‖ := norm_sub_le _ _
        rw [hr2norm, norm_mul, show ‖(starRingEnd ℂ) u‖ = ‖u‖ by simp] at h1
        nlinarith [h1, hS_lt u hu, hxs, norm_nonneg u, norm_nonneg ((x:ℂ) - u)]
      rw [norm_div, norm_mul, show ‖(r:ℂ)‖ = r by simp [abs_of_pos hr], ← mul_div_assoc,
        le_div_iff₀ hdpos]
      nlinarith [hdle, norm_nonneg ((x:ℂ) - u)]
  -- bound on h by the maximum modulus principle
  have hDiffBall : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    (hh_an5.differentiableOn).mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hContCl : ContinuousOn h (Metric.closedBall 0 r) :=
    hh_an5.continuousOn.mono (Metric.closedBall_subset_ball hr5)
  have hDiffCl : DiffContOnCl ℂ h (Metric.ball 0 r) := DiffContOnCl.mk_ball hDiffBall hContCl
  have hhM : ∀ z ∈ Metric.ball 0 r, ‖h z‖ ≤ M := by
    intro z hz
    have hzcl : z ∈ closure (Metric.ball 0 r) := by
      rw [closure_ball 0 (ne_of_gt hr)]; exact Metric.ball_subset_closedBall hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hDiffCl
      (fun w hw => by
        rw [frontier_ball 0 (ne_of_gt hr), Metric.mem_sphere, dist_zero_right] at hw
        have hwm : w ∈ Metric.closedBall 0 r := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hw.le
        have heq := hφ_eq_bh_cl w hwm
        have hb1 : ‖b w‖ = 1 := hb_circ w hw
        have : ‖h w‖ = ‖φ w‖ := by rw [heq, norm_mul, hb1, one_mul]
        rw [this]
        exact hbound w (by rw [Metric.mem_ball, dist_zero_right, hw]; exact hr3)) hzcl
  have hφ_eq_bh : ∀ z ∈ Metric.ball 0 r, φ z = b z * h z :=
    fun z hz => hφ_eq_bh_cl z (Metric.ball_subset_closedBall hz)
  have hh0 : 1 ≤ ‖h 0‖ := by
    have h0cl : (0:ℂ) ∈ Metric.closedBall 0 r := by
      rw [Metric.mem_closedBall, dist_zero_right]; simpa using hr.le
    have h0ball : (0:ℂ) ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]; simpa using hr
    have heq := hφ_eq_bh_cl 0 h0cl
    have hb0ne : b 0 ≠ 0 := by intro hb0; rw [hb0, zero_mul] at heq; exact hφ0ne heq
    have hb0pos : 0 < ‖b 0‖ := norm_pos_iff.mpr hb0ne
    have hb0le : ‖b 0‖ ≤ 1 := hb_le1 0 h0ball
    have hnorm : ‖h 0‖ = ‖φ 0‖ / ‖b 0‖ := by
      rw [show ‖φ 0‖ = ‖b 0‖ * ‖h 0‖ by rw [heq, norm_mul],
        mul_div_cancel_left₀ ‖h 0‖ (ne_of_gt hb0pos)]
    rw [hnorm, le_div_iff₀ hb0pos]
    nlinarith [hb0le, hφ0]
  -- counting bound
  have hNreal : (N : ℝ) = ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) := by
    have h1 : (N : ℝ) = ∑ u ∈ S, (dn u : ℝ) := by
      rw [show N = ∑ u ∈ S, dn u from rfl]
      push_cast
      rfl
    rw [h1, finsum_eq_sum_of_support_subset (fun u : ℂ => ((D u : ℤ) : ℝ)) ?_]
    · apply Finset.sum_congr rfl
      intro u hu
      dsimp only [dn]
      exact_mod_cast (Int.toNat_of_nonneg (hD_nonneg u))
    · intro u hu
      rw [Function.mem_support] at hu
      rw [hS_coe, Function.mem_support]
      exact fun h => hu (by exact_mod_cast h)
  have hDsupp : Function.HasFiniteSupport (fun u : ℂ => ((D u : ℤ) : ℝ)) := by
    show (Function.support (fun u : ℂ => ((D u : ℤ) : ℝ))).Finite
    exact h3.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      exact fun h => hu (by exact_mod_cast h))
  have hCdsupp : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ)) := by
    show (Function.support (fun u : ℂ =>
      ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ))).Finite
    refine (MeromorphicOn.divisor_support_finite_of_subset
      (hφ.mono (Metric.closedBall_subset_ball hr5)).meromorphicOn
      (isCompact_closedBall 0 r) (subset_refl _)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    exact fun h => hu (by exact_mod_cast h)
  have hsum_le : ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) ≤
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ) := by
    apply finsum_le_finsum' hDsupp hCdsupp
    intro u
    change ((D u : ℤ) : ℝ) ≤ ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ)
    by_cases hu : u ∈ Metric.ball 0 r
    · have h1 : D u = (MeromorphicOn.divisor φ (Metric.closedBall 0 r)) u := by
        rw [show D u = MeromorphicOn.divisor φ (Metric.ball 0 r) u from rfl,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (hφ.mono (Metric.ball_subset_ball (le_of_lt hr5))) hu,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (hφ.mono (Metric.closedBall_subset_ball hr5))
            (Metric.ball_subset_closedBall hu)]
      exact_mod_cast le_of_eq h1
    · have h1 : D u = 0 := by
        rw [show D u = MeromorphicOn.divisor φ (Metric.ball 0 r) u from rfl,
          MeromorphicOn.divisor_def]
        simp [hu]
      have hle : D u ≤ (MeromorphicOn.divisor φ (Metric.closedBall 0 r)) u :=
        h1.symm ▸ MeromorphicOn.AnalyticOnNhd.divisor_nonneg
          (hφ.mono (Metric.closedBall_subset_ball hr5)) u
      exact_mod_cast hle
  have hcount : (N : ℝ) * Real.log (3 / r) ≤ Real.log M := by
    have havg := circleAverage_log_norm_le_log_of_bound_three hM1 hφ hbound
    have hJ := divisor_sum_le_circleAverage (c := 0) (r := r) (R := 3) (B := Real.log M)
      hr hr3 (hφ.mono (Metric.closedBall_subset_ball (by norm_num))) hφ0ne havg
    have hlogpos : 0 < Real.log (3 / r) := by
      apply Real.log_pos; rw [one_lt_div hr]; exact hr3
    rw [hNreal]
    calc (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ)) * Real.log (3 / r)
        ≤ (∑ᶠ u : ℂ, ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ))
            * Real.log (3 / r) := mul_le_mul_of_nonneg_right hsum_le hlogpos.le
      _ ≤ ((Real.log M - Real.log ‖φ 0‖) / Real.log (3 / r)) * Real.log (3 / r) :=
          mul_le_mul_of_nonneg_right hJ hlogpos.le
      _ = Real.log M - Real.log ‖φ 0‖ := div_mul_cancel₀ _ (ne_of_gt hlogpos)
      _ ≤ Real.log M := by have := Real.log_nonneg hφ0; linarith
  have hpoly3 : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → ‖P.eval (x:ℂ)‖ ≤ (3:ℝ)^N * ‖b (x:ℂ)‖ := by
    intro x hx
    have h := hpoly x hx
    have hr3v : r + 1 = 3 := by rw [hr_def]; norm_num
    rwa [hr3v] at h
  refine ⟨N, b, h, P, hPmonic, hPdeg, hb_an, hh_an, hh_ne, hφ_eq_bh,
    hb_circ, hb_le1, hpoly3, hhM, hh0, hcount⟩


/-- **Kovrijkine ratio lemma, radius `3` version.**
`φ` analytic on `ball 0 5`, bounded by `M` on `ball 0 3`, `1 ≤ ‖φ 0‖`, `E ⊆ [0,1]` of positive
measure, `|φ| ≤ a` on `E`; then `‖φ x‖ ≤ (10^6/|E|)^{10^6 log M} a` for `x ∈ [0,1]`. -/
private theorem kovrijkine_ratio_three (φ : ℂ → ℂ) (M a : ℝ) (hM : 1 ≤ M)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 5))
    (hbound : ∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖φ z‖ ≤ M)
    (h0 : 1 ≤ ‖φ 0‖)
    (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (0:ℝ) 1)
    (hEpos : 0 < (volume E).toReal)
    (ha : ∀ x : ℝ, x ∈ E → ‖φ (x:ℂ)‖ ≤ a) :
    ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 →
      ‖φ (x:ℂ)‖ ≤ ((10:ℝ)^6 / (volume E).toReal) ^ ((10:ℝ)^6 * Real.log M) * a := by
  intro x hx
  obtain ⟨N, b, h, P, hPmonic, hPdeg, hb_an, hh_an, hh_ne, hφ_eq_bh, hb_circ, hb_le1,
    hpoly, hhM, hh0, hcount⟩ := kovrijkine_blaschke_core_three φ M hφ hbound hM h0
  set v : ℝ := (volume E).toReal with hvdef
  have hvpos : 0 < v := hEpos
  have hv1 : v ≤ 1 := by
    have hIcc : volume (Set.Icc (0:ℝ) 1) = (1 : ℝ≥0∞) := by rw [Real.volume_Icc]; norm_num
    have hle : volume E ≤ (1 : ℝ≥0∞) := hIcc ▸ measure_mono hEsub
    calc v = (volume E).toReal := rfl
      _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by norm_num) hle
      _ = 1 := by norm_num
  have hx3 : (x:ℂ) ∈ Metric.ball 0 3 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have : |x| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
    linarith
  have hφx : ‖φ x‖ ≤ M := hbound _ hx3
  have hharn : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (M^4)⁻¹ ≤ ‖h t‖ :=
    harnack_lower_bound_two h M hM hh_an hh_ne hhM hh0
  have hBdd : BddAbove ((fun t : ℝ => ‖φ t‖) '' E) := by
    refine ⟨M, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine hbound (t:ℂ) ?_
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hEsub ht
    have : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [h1.1], h1.2⟩
    linarith
  set S : ℝ := sSup ((fun t : ℝ => ‖φ t‖) '' E) with hSdef
  have hEne : E.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hEe
    have h0 : v = 0 := by rw [hvdef, hEe]; simp
    exact absurd h0 (ne_of_gt hEpos)
  have hSbound : (M^4)⁻¹ * (v/240)^N ≤ S := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- N = 0
      obtain ⟨t, htE⟩ := hEne
      have htIcc := hEsub htE
      have ht2 : (t:ℂ) ∈ Metric.ball 0 2 := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        have : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [htIcc.1], htIcc.2⟩
        linarith
      have hP1 : P = 1 := by
        have h := Polynomial.eq_C_of_natDegree_eq_zero (hPdeg.trans hN0)
        have hc0 : P.coeff 0 = 1 := by
          have := hPmonic.coeff_natDegree
          rw [hPdeg, hN0] at this
          exact this
        rw [h, hc0]; simp
      have hbt1 : (1:ℝ) ≤ ‖b (t:ℂ)‖ := by
        have h1 := hpoly t htIcc
        rw [hP1, hN0] at h1
        simpa using h1
      have hbt2 : ‖b (t:ℂ)‖ ≤ 1 := hb_le1 (t:ℂ) ht2
      have hbt : ‖b (t:ℂ)‖ = 1 := le_antisymm hbt2 hbt1
      have hle := le_csSup hBdd (show ‖φ t‖ ∈ ((fun s : ℝ => ‖φ s‖) '' E) from ⟨t, htE, rfl⟩)
      have hprod : ‖φ t‖ = ‖b (t:ℂ)‖ * ‖h t‖ := by
        rw [hφ_eq_bh (t:ℂ) ht2, norm_mul]
      rw [hprod, hbt, one_mul] at hle
      have ht' := hharn t (Set.Icc_subset_Icc (by norm_num) (by norm_num) htIcc)
      rw [hN0, pow_zero, mul_one] at *
      linarith [hle, ht']
    · -- N ≥ 1
      have hN1 : 1 ≤ N := hNpos
      have hfind : ∃ t ∈ E, (v/240)^N < ‖b (t:ℂ)‖ := by
        by_contra hcon
        push_neg at hcon
        have hPbd : ∀ t ∈ E, ‖P.eval (t:ℂ)‖ ≤ (3:ℝ)^N * (v/240)^N := by
          intro t ht
          have h1 := hpoly t (hEsub ht)
          have h2 : (3:ℝ)^N * ‖b (t:ℂ)‖ ≤ (3:ℝ)^N * (v/240)^N :=
            mul_le_mul_of_nonneg_left (hcon t ht) (by positivity)
          linarith
        have hlev := monic_level_set_Icc_volume_le N hN1 P hPmonic hPdeg
          ((3:ℝ)^N * (v/240)^N) (by positivity) E hE
          (hEsub.trans (Set.Icc_subset_Icc (by norm_num) (by norm_num))) hPbd
        rw [← hvdef] at hlev
        rw [← mul_pow] at hlev
        have hroot : ((3 * (v/240)) ^ N : ℝ) ^ ((1:ℝ)/N) = 3 * (v/240) := by
          rw [← Real.rpow_natCast (3 * (v/240)) N, ← Real.rpow_mul (by positivity)]
          have h1 : ((N:ℝ) * ((1:ℝ)/N)) = 1 := by field_simp
          rw [h1, Real.rpow_one]
        rw [hroot] at hlev
        have h2 : (30:ℝ) * (3 * (v/240)) = 3 * v / 8 := by ring
        rw [h2] at hlev
        linarith [hvpos]
      obtain ⟨t, htE, hbτ⟩ := hfind
      have htIcc := hEsub htE
      have ht2 : (t:ℂ) ∈ Metric.ball 0 2 := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        have : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [htIcc.1], htIcc.2⟩
        linarith
      have hle := le_csSup hBdd (show ‖φ t‖ ∈ ((fun s : ℝ => ‖φ s‖) '' E) from ⟨t, htE, rfl⟩)
      have hprod : ‖φ t‖ = ‖b (t:ℂ)‖ * ‖h t‖ := by
        rw [hφ_eq_bh (t:ℂ) ht2, norm_mul]
      rw [hprod] at hle
      have h1 : (v/240)^N * (M^4)⁻¹ ≤ ‖b (t:ℂ)‖ * ‖h t‖ :=
        mul_le_mul hbτ.le (hharn t (Set.Icc_subset_Icc (by norm_num) (by norm_num) htIcc))
          (by positivity) (by positivity)
      linarith [hle, h1]
  -- conclusion
  have hSle : S ≤ a := by
    refine csSup_le ⟨_, ⟨(hEne.some), hEne.some_mem, rfl⟩⟩ ?_
    rintro y ⟨t, ht, rfl⟩
    exact ha t ht
  have hNrel : (N:ℝ) * Real.log (4/3) ≤ Real.log M := by
    have h1 : Real.log (4/3) ≤ Real.log (3/2) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h2 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [hcount, h1, h2]
  have hgoal : (v/100) ^ (10 * Real.log M) ≤ (v/240)^N :=
    ratio_arith v M hvpos (by linarith) hM N hNrel
  have hApos : 0 < (v/100) ^ (10 * Real.log M) := Real.rpow_pos_of_pos (by positivity) _
  have hM4pos : 0 < (M^4)⁻¹ := by positivity
  have hSbound' : (v/240)^N * (M^4)⁻¹ ≤ S := by
    rw [mul_comm]; exact hSbound
  have hSge : (v/100) ^ (10 * Real.log M) * (M^4)⁻¹ ≤ S :=
    le_trans (mul_le_mul_of_nonneg_right hgoal hM4pos.le) hSbound'
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hX : (100/v) ^ (10 * Real.log M) * (v/100) ^ (10 * Real.log M) = 1 := by
    rw [show (100:ℝ)/v = (v/100)⁻¹ by field_simp]
    rw [Real.inv_rpow (by positivity)]
    exact inv_mul_cancel₀ (ne_of_gt hApos)
  have hkey : M ≤ (100/v) ^ (10 * Real.log M) * M^5 * a := by
    have h3 : (0:ℝ) ≤ (100/v) ^ (10 * Real.log M) * M^5 := by positivity
    have h4 : (100/v) ^ (10 * Real.log M) * M^5 * ((v/100) ^ (10 * Real.log M) * (M^4)⁻¹) ≤
        (100/v) ^ (10 * Real.log M) * M^5 * S :=
      mul_le_mul_of_nonneg_left hSge h3
    have h5 : (100/v) ^ (10 * Real.log M) * M^5 * ((v/100) ^ (10 * Real.log M) * (M^4)⁻¹) = M := by
      calc (100/v) ^ (10 * Real.log M) * M^5 * ((v/100) ^ (10 * Real.log M) * (M^4)⁻¹)
          = ((100/v) ^ (10 * Real.log M) * (v/100) ^ (10 * Real.log M)) * (M^5 * (M^4)⁻¹) := by
            ring
        _ = 1 * (M^5 * (M^4)⁻¹) := by rw [hX]
        _ = M^5 * (M^4)⁻¹ := one_mul _
        _ = M := by
            have hMne : M ≠ 0 := ne_of_gt hM0
            field_simp
    rw [h5] at h4
    calc M ≤ (100/v) ^ (10 * Real.log M) * M^5 * S := h4
      _ ≤ (100/v) ^ (10 * Real.log M) * M^5 * a := mul_le_mul_of_nonneg_left hSle h3
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) (ha (hEne.some) hEne.some_mem)
  calc ‖φ (x:ℂ)‖ ≤ M := hφx
    _ ≤ (100/v) ^ (10 * Real.log M) * M^5 * a := hkey
    _ ≤ ((10:ℝ)^6 / v) ^ ((10:ℝ)^6 * Real.log M) * a := ratio_absorb hvpos (by linarith) hM ha0
    _ = ((10:ℝ)^6 / (volume E).toReal) ^ ((10:ℝ)^6 * Real.log M) * a := by rw [← hvdef]



/-- The unit cube of `ℝ^d` has volume at most `1`; in particular any measurable subset has
total mass at most `1`. -/
private lemma cube_toReal_le_one (d : ℕ) (E : Set (EuclideanSpace ℝ (Fin d)))
    (hEsub : E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) :
    (volume E).toReal ≤ 1 := by
  have hvolQen : volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
      = (1:ℝ≥0∞) := by
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) volume volume := by
      simpa using (PiLp.volume_preserving_ofLp (Fin d))
    have hset : {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        = (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) ⁻¹'
          (Set.pi Set.univ (fun i : Fin d => Set.Icc (0:ℝ) 1)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Icc]
    rw [hset, hmp.measure_preimage
      (MeasurableSet.univ_pi (fun i => measurableSet_Icc)).nullMeasurableSet]
    rw [show (Set.pi Set.univ (fun i : Fin d => Set.Icc (0:ℝ) 1))
        = Set.Icc (0 : Fin d → ℝ) 1 from (Set.pi_univ_Icc 0 1)]
    rw [Real.volume_Icc_pi]
    simp
  have hne : volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} ≠ ⊤ := by
    rw [hvolQen]; norm_num
  simpa [hvolQen] using ENNReal.toReal_mono hne (measure_mono hEsub)

/-- The core reduction at a cube point `y` with `‖F y‖ ≥ 1`: the geometric pigeonhole produces
a segment along which the one-variable Kovrijkine estimate (radius `3` version) applies. -/
private theorem kovrijkine_key (d : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hpig : ∀ (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)),
      y ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      MeasurableSet E →
      E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      0 < (volume E).toReal →
      ∃ v : EuclideanSpace ℝ (Fin d),
        (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
          y + t • v ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) ∧
        c * (volume E).toReal ≤
          (volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ y + t • v ∈ E}).toReal)
    (F : (Fin d → ℂ) → ℂ) (M a : ℝ) (hM : 1 ≤ M) (ha : 0 ≤ a)
    (hF : Differentiable ℂ F) (hbnd : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hEmeas : MeasurableSet E)
    (hEsub : E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
    (hEpos : 0 < (volume E).toReal)
    (haE : ∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
    (hy1 : 1 ≤ ‖F (fun i => (y i : ℂ))‖) :
    ‖F (fun i => (y i : ℂ))‖ ≤
      ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log M) * a := by
  have hδle1 : (volume E).toReal ≤ 1 := cube_toReal_le_one d E hEsub
  set A : ℝ := ‖F (fun i => (y i : ℂ))‖ with hAdef
  have hA1 : 1 ≤ A := hy1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hyle : ∀ i, |y i| ≤ 1 := by
    intro i; rw [abs_le]; exact ⟨by linarith [(hy i).1], (hy i).2⟩
  have hAleM : A ≤ M := by
    rw [hAdef]
    refine hbnd _ fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hyle i]
  obtain ⟨v, hvseg, hvmass⟩ := hpig E y hy hEmeas hEsub hEpos
  have hvle : ∀ i, |v i| ≤ 1 := by
    intro i
    have h2' : 0 ≤ y i + v i ∧ y i + v i ≤ 1 := by
      have h1 := (hvseg 1 (by norm_num)) i
      simp only [one_smul] at h1
      exact h1
    rw [abs_le]
    constructor <;> linarith [h2'.1, h2'.2, (hy i).1, (hy i).2]
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ y + t • v ∈ E} with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact measurableSet_Icc.inter (hEmeas.preimage
      (continuous_const.add (continuous_id.smul continuous_const)).measurable)
  have hSsub : S ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ht.1
  have hSle1 : (volume S).toReal ≤ 1 := by
    have h : volume S ≤ volume (Set.Icc (0:ℝ) 1) := measure_mono hSsub
    have h2 : (volume (Set.Icc (0:ℝ) 1)).toReal = 1 := by rw [Real.volume_Icc]; norm_num
    calc (volume S).toReal ≤ (volume (Set.Icc (0:ℝ) 1)).toReal :=
          ENNReal.toReal_mono (by rw [Real.volume_Icc]; norm_num) h
      _ = 1 := h2
  have hSge : c * (volume E).toReal ≤ (volume S).toReal := hvmass
  have hSpos : 0 < (volume S).toReal := lt_of_lt_of_le (mul_pos hc hEpos) hSge
  -- the one-variable function
  set Ψ : ℂ → ℂ := fun z => F (fun i => ((y i : ℂ) + z * (v i : ℂ))) / ((A : ℝ) : ℂ) with hΨdef
  have hΨdiff : Differentiable ℂ Ψ := by
    rw [hΨdef]
    refine Differentiable.div_const ?_ _
    refine hF.comp ?_
    fun_prop
  have hΨan : AnalyticOnNhd ℂ Ψ (Metric.ball 0 5) :=
    (hΨdiff.differentiableOn).analyticOnNhd Metric.isOpen_ball
  have hΨbd : ∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖Ψ z‖ ≤ M / A := by
    intro z hz
    have hz3 : ‖z‖ < 3 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [hΨdef, norm_div, Complex.norm_of_nonneg hApos.le]
    refine div_le_div_of_nonneg_right ?_ hApos.le
    refine hbnd _ fun i => ?_
    have h1 : ‖((y i : ℂ) + z * (v i : ℂ))‖ ≤ 4 := by
      calc ‖((y i : ℂ) + z * (v i : ℂ))‖
          ≤ ‖((y i : ℂ))‖ + ‖z * (v i : ℂ)‖ := norm_add_le _ _
        _ = |y i| + ‖z‖ * |v i| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
              Real.norm_eq_abs]
        _ ≤ 1 + 3 * 1 := by
            have h2 := hyle i; have h3 := hvle i
            nlinarith [norm_nonneg z]
        _ ≤ 4 := by norm_num
    simpa using h1
  have hΨ0 : 1 ≤ ‖Ψ 0‖ := by
    rw [hΨdef]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [norm_div, Complex.norm_of_nonneg hApos.le, ← hAdef, div_self (ne_of_gt hApos)]
  have hΨS : ∀ t : ℝ, t ∈ S → ‖Ψ (t:ℂ)‖ ≤ a / A := by
    intro t ht
    rw [hΨdef, norm_div, Complex.norm_of_nonneg hApos.le]
    refine div_le_div_of_nonneg_right ?_ hApos.le
    have hEq : (fun i : Fin d => ((y i : ℂ) + (t:ℂ) * (v i : ℂ)))
        = (fun i => (((y + t • v) i : ℝ) : ℂ)) := by
      funext i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact haE (y + t • v) ht.2
  have hMdiv : 1 ≤ M / A := by
    rw [le_div_iff₀ hApos]; linarith
  have hadiv : 0 ≤ a / A := div_nonneg ha hApos.le
  have hconcl := kovrijkine_ratio_three Ψ (M / A) (a / A) hMdiv hΨan hΨbd hΨ0 S hSmeas hSsub hSpos hΨS
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h1 := hconcl 0 h0mem
  rw [hΨdef] at h1
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h1
  have hFyA : ‖F (fun i => (y i : ℂ)) / ((A:ℝ):ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_of_nonneg hApos.le, ← hAdef, div_self (ne_of_gt hApos)]
  have h2 : (1:ℝ) ≤ ((10:ℝ)^6 / (volume S).toReal) ^ ((10:ℝ)^6 * Real.log (M / A)) * (a / A) := by
    rw [← hFyA]; exact h1
  have hA' : A ≤ ((10:ℝ)^6 / (volume S).toReal) ^ ((10:ℝ)^6 * Real.log (M / A)) * a := by
    have h3 := mul_le_mul_of_nonneg_right h2 hApos.le
    rw [mul_assoc, div_mul_cancel₀ a (ne_of_gt hApos), one_mul] at h3
    exact h3
  have hbase1 : (1:ℝ) ≤ (10:ℝ)^6 / (volume S).toReal := by
    rw [le_div_iff₀ hSpos]; nlinarith [hSle1]
  have hbase2 : (10:ℝ)^6 / (volume S).toReal ≤ (10:ℝ)^6 / (c * (volume E).toReal) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hEpos) hSge
  have hlog : Real.log (M / A) ≤ Real.log M := by
    apply Real.log_le_log (div_pos (lt_of_lt_of_le zero_lt_one hM) hApos)
    rw [div_le_iff₀ hApos]; nlinarith [hA1, hM]
  have hexp : (10:ℝ)^6 * Real.log (M / A) ≤ (10:ℝ)^6 * Real.log M := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ M / A)
    nlinarith [hlog]
  have hcE : c * (volume E).toReal ≤ 1 := by
    have h1 : c * (volume E).toReal ≤ c * 1 := mul_le_mul_of_nonneg_left hδle1 hc.le
    linarith [hc1]
  have hbasege : (1:ℝ) ≤ (10:ℝ)^6 / (c * (volume E).toReal) := by
    rw [le_div_iff₀ (mul_pos hc hEpos)]
    nlinarith [hcE]
  have hstep1 : ((10:ℝ)^6 / (volume S).toReal) ^ ((10:ℝ)^6 * Real.log (M / A)) ≤
      ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log (M / A)) :=
    Real.rpow_le_rpow (by positivity) hbase2 (mul_nonneg (by norm_num) (Real.log_nonneg hMdiv))
  have hstep2 : ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log (M / A)) ≤
      ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log M) :=
    Real.rpow_le_rpow_of_exponent_le hbasege hexp
  calc A ≤ ((10:ℝ)^6 / (volume S).toReal) ^ ((10:ℝ)^6 * Real.log (M / A)) * a := hA'
    _ ≤ ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log (M / A)) * a :=
        mul_le_mul_of_nonneg_right hstep1 ha
    _ ≤ ((10:ℝ)^6 / (c * (volume E).toReal)) ^ ((10:ℝ)^6 * Real.log M) * a :=
        mul_le_mul_of_nonneg_right hstep2 ha


/-- Assembly of the higher dimensional Kovrijkine lemma from the geometric pigeonhole. -/
private theorem kovrijkine_main (d : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hpig : ∀ (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)),
      y ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      MeasurableSet E →
      E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      0 < (volume E).toReal →
      ∃ v : EuclideanSpace ℝ (Fin d),
        (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
          y + t • v ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) ∧
        c * (volume E).toReal ≤
          (volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ y + t • v ∈ E}).toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a →
      Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) →
      1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal →
        (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (C / (volume E).toReal) ^ (C * Real.log M) * a := by
  refine ⟨max ((10:ℝ)^6) ((10:ℝ)^6 / c), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro F M a hM ha hF hbnd hF0 E hEmeas hEsub hEpos haE x hx
  set C : ℝ := max ((10:ℝ)^6) ((10:ℝ)^6 / c) with hCdef
  set δ : ℝ := (volume E).toReal with hδdef
  have hδpos : 0 < δ := hEpos
  have hC1 : (1:ℝ) ≤ C := le_trans (by norm_num) (le_max_left _ _)
  have hδ1 : δ ≤ 1 := cube_toReal_le_one d E hEsub
  have hkey := fun (y : EuclideanSpace ℝ (Fin d))
      (hy : y ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
      (hy1 : 1 ≤ ‖F (fun i => (y i : ℂ))‖) =>
    kovrijkine_key d c hc hc1 hpig F M a hM ha hF hbnd E hEmeas hEsub hEpos haE y hy hy1
  have h0Q : (0 : EuclideanSpace ℝ (Fin d)) ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    intro i; simp
  have hF0' : (1:ℝ) ≤ ‖F (fun i => (((0 : EuclideanSpace ℝ (Fin d)) i) : ℂ))‖ := by
    have hz : (fun i : Fin d => (((0 : EuclideanSpace ℝ (Fin d)) i) : ℂ)) = (0 : Fin d → ℂ) := by
      funext i; simp
    rw [hz]; exact hF0
  have hB : 1 ≤ ((10:ℝ)^6 / (c * δ)) ^ ((10:ℝ)^6 * Real.log M) * a :=
    le_trans hF0' (hkey 0 h0Q hF0')
  have hfin : ‖F (fun i => (x i : ℂ))‖ ≤
      ((10:ℝ)^6 / (c * δ)) ^ ((10:ℝ)^6 * Real.log M) * a := by
    by_cases h1 : (1:ℝ) ≤ ‖F (fun i => (x i : ℂ))‖
    · exact hkey x hx h1
    · push_neg at h1; linarith
  have hbase_le : (10:ℝ)^6 / (c * δ) ≤ C / δ := by
    have h1 : (10:ℝ)^6 / (c * δ) = ((10:ℝ)^6 / c) / δ := (div_div _ _ _).symm
    rw [h1, div_le_div_iff_of_pos_right hδpos]
    exact le_max_right _ _
  have hexp_le : (10:ℝ)^6 * Real.log M ≤ C * Real.log M :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hM)
  have hbaseC : (1:ℝ) ≤ C / δ := by
    rw [le_div_iff₀ hδpos]
    nlinarith [hC1, hδ1]
  have hstep : ((10:ℝ)^6 / (c * δ)) ^ ((10:ℝ)^6 * Real.log M) ≤ (C / δ) ^ (C * Real.log M) := by
    refine le_trans (Real.rpow_le_rpow (by positivity) hbase_le
      (mul_nonneg (by norm_num) (Real.log_nonneg hM))) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbaseC hexp_le
  calc ‖F (fun i => (x i : ℂ))‖ ≤ ((10:ℝ)^6 / (c * δ)) ^ ((10:ℝ)^6 * Real.log M) * a := hfin
    _ ≤ (C / δ) ^ (C * Real.log M) * a := mul_le_mul_of_nonneg_right hstep ha
    _ = (C / (volume E).toReal) ^ (C * Real.log M) * a := by rw [hδdef]


/-- **Kovrijkine's lemma in `d` complex variables.**  There is a constant `C = C(d) > 0` such
that for every entire `F : ℂ^d → ℂ` bounded by `M ≥ 1` on the polydisc of radius `4`, with
`‖F 0‖ ≥ 1`, and every measurable `E` in the unit cube on which `‖F‖ ≤ a`, one has
`‖F x‖ ≤ (C / |E|)^{C log M} a` on the whole unit cube. -/
theorem kovrijkine_d (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a →
      Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) →
      1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal →
        (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (C / (volume E).toReal) ^ (C * Real.log M) * a := by
  obtain ⟨c, hc, hc1, hpig⟩ :=
    Commons.Measure.EuclideanSpace.exists_segment_large_intersection d
  exact kovrijkine_main d c hc hc1 hpig

end Commons.Analysis.Complex
