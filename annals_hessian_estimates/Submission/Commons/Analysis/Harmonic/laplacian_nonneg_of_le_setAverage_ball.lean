import Mathlib
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_two_half_le
import Submission.Commons.Analysis.Measure.setAverage_ball_add
import Submission.Commons.Analysis.Measure.setAverage_mul_const
import Submission.Commons.Analysis.Harmonic.setAverage_ball_bilinear

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace Commons.Analysis.Harmonic

set_option linter.style.haveILetI false

/-! ## Auxiliary set-average lemmas -/

theorem setAverage_add_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → ℝ} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    (⨍ x in s, (f x + g x) ∂μ) = (⨍ x in s, f x ∂μ) + (⨍ x in s, g x ∂μ) := by
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_add hf hg, smul_add]

theorem setAverage_mul_const_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (c : ℝ) (f : α → ℝ) :
    (⨍ x in s, c * f x ∂μ) = c * ⨍ x in s, f x ∂μ := by
  rw [setAverage_eq, setAverage_eq, integral_const_mul]
  ring

/-- The average of the identity over a ball centred at `0` is `0`. -/
theorem setAverage_ball_self_eq_zero {n : ℕ} (r : ℝ) :
    (⨍ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, x) = 0 := by
  rw [setAverage_eq]
  have h : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, x) = 0 := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    have hF : ∀ x, (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator (fun y => y) (-x)
        = - (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator (fun y => y) x := by
      intro x
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      · have hnx : -x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
          simp only [mem_ball, dist_eq_norm, sub_zero] at hx ⊢
          simpa using hx
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hnx]
      · have hnx : -x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
          intro h
          apply hx
          simp only [mem_ball, dist_eq_norm, sub_zero] at h ⊢
          simpa using h
        simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnx]
    let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator (fun y => y)
    have hF : ∀ x, F (-x) = - F x := by
      intro x
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      · have hnx : -x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
          simp only [mem_ball, dist_eq_norm, sub_zero] at hx ⊢
          simpa using hx
        simp [F, Set.indicator_of_mem hx, Set.indicator_of_mem hnx]
      · have hnx : -x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
          intro h
          apply hx
          simp only [mem_ball, dist_eq_norm, sub_zero] at h ⊢
          simpa using h
        simp [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hnx]
    have h1 : (∫ x, F (-x)) = ∫ x, F x := MeasureTheory.integral_neg_eq_self F _
    have h2 : (∫ x, F (-x)) = - ∫ x, F x := by
      rw [← MeasureTheory.integral_neg]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hF)
    rw [h1] at h2
    rw [eq_neg_iff_add_eq_zero] at h2
    have hzero : (∫ x, F x) = 0 := by
      have h3 : (2 : ℝ) • (∫ x, F x) = 0 := by rw [two_smul ℝ]; exact h2
      exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
    simpa [F] using hzero
  rw [h, smul_zero]

/-- Norm bound for a set average. -/
theorem norm_setAverage_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} {C : ℝ} (hfin : μ s < ∞) (hpos : 0 < μ.real s)
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖⨍ x in s, f x ∂μ‖ ≤ C := by
  rw [setAverage_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, ← div_eq_inv_mul,
    div_le_iff₀ hpos]
  exact MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hC




/-! ## The trace identity -/

theorem laplacian_eq_sum_fderiv_fderiv {n : ℕ} {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian v c
      = ∑ i : Fin n,
          (fderiv ℝ (fderiv ℝ v) c) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  simp

/-! ## The main theorem -/

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem laplacian_nonneg_of_le_setAverage_ball {n : ℕ} {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : ContDiff ℝ 2 v)
    (h : ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r → v c ≤ ⨍ y in ball c r, v y)
    (c : EuclideanSpace ℝ (Fin n)) :
    0 ≤ Laplacian.laplacian v c := by
  by_cases hn : n = 0
  · subst hn
    haveI : IsEmpty (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)))) := by
      have hf : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 := by
        simp [finrank_euclideanSpace]
      rw [hf]; infer_instance
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis v]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact le_refl 0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  suffices key : ∀ ε : ℝ, 0 < ε →
      0 ≤ Laplacian.laplacian v c / (2 * ((n : ℝ) + 2)) + ε by
    by_contra hconcl
    push Not at hconcl
    have hDpos : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by positivity
    have hneg : Laplacian.laplacian v c / (2 * ((n : ℝ) + 2)) < 0 :=
      div_neg_of_neg_of_pos hconcl hDpos
    have hε : (0 : ℝ) < -(Laplacian.laplacian v c / (2 * ((n : ℝ) + 2))) / 2 := by linarith
    have hkey := key _ hε
    linarith
  intro ε hε
  set M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ v) c with hM₀
  have hvcont : Continuous v := hv.continuous
  have hΔ : Laplacian.laplacian v c
      = ∑ i : Fin n, M₀ (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    rw [laplacian_eq_sum_fderiv_fderiv, ← hM₀]
  -- Continuity of the Hessian, giving the `ε`-closeness radius
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w - c‖ < δ → ‖fderiv ℝ (fderiv ℝ v) w - M₀‖ ≤ ε := by
    have hD2cont : Continuous (fderiv ℝ (fderiv ℝ v)) :=
      ((hv.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
    have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ v)) c := hD2cont.continuousAt
    have hb : Metric.ball (fderiv ℝ (fderiv ℝ v) c) ε ∈ 𝓝 (fderiv ℝ (fderiv ℝ v) c) :=
      Metric.ball_mem_nhds (fderiv ℝ (fderiv ℝ v) c) hε
    have hev : ∀ᶠ w in 𝓝 c, fderiv ℝ (fderiv ℝ v) w ∈ Metric.ball (fderiv ℝ (fderiv ℝ v) c) ε :=
      hcont hb
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    refine ⟨δ, hδpos, fun w hw => ?_⟩
    have hw' : dist w c < δ := by rwa [dist_eq_norm w c]
    have h0 : fderiv ℝ (fderiv ℝ v) w ∈ Metric.ball (fderiv ℝ (fderiv ℝ v) c) ε := hδ hw'
    have h1 : dist (fderiv ℝ (fderiv ℝ v) w) (fderiv ℝ (fderiv ℝ v) c) < ε := by
      simpa [Metric.mem_ball] using h0
    rw [dist_eq_norm (fderiv ℝ (fderiv ℝ v) w) (fderiv ℝ (fderiv ℝ v) c)] at h1
    rw [hM₀]
    exact le_of_lt h1
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrδ : r < δ := by rw [hr]; linarith
  have hballfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball c r) < ∞ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall c r).measure_lt_top
  have hballpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball c r) := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume c hrpos).ne' (ne_of_lt hballfin)
  -- The Taylor remainder and its bound
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    v y - v c - (fderiv ℝ v c) (y - c) - (1 / 2 : ℝ) * M₀ (y - c) (y - c) with hF
  have hFbound : ∀ y ∈ closedBall c r, ‖F y‖ ≤ ε * r ^ 2 := by
    intro y hy
    have hyr : ‖y - c‖ ≤ r := by
      have h' := mem_closedBall.mp hy
      rwa [dist_eq_norm y c] at h'
    have hy2 : ‖y - c‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (y - c)]
    have hcy : c + (y - c) = y := by abel
    have hb : |v y - v c - (fderiv ℝ v c) (y - c)
        - (1 / 2 : ℝ) * M₀ (y - c) (y - c)| ≤ ε * ‖y - c‖ ^ 2 := by
      have h0 := Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_two_half_le
        (f := v) (x := c) (y := y - c) (B := M₀) hε.le
        (fun t _ => hv.contDiffAt) (fun t ht => ?_)
      · rwa [hcy] at h0
      · apply hδ
        have ht0 : 0 ≤ t := ht.1
        have htn : ‖(c + t • (y - c)) - c‖ = t * ‖y - c‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        rw [htn]
        nlinarith [ht.2, hyr, norm_nonneg (y - c), hrδ]
    rw [Real.norm_eq_abs, hF]
    exact hb.trans (mul_le_mul_of_nonneg_left hy2 hε.le)
  have hFavg : ‖⨍ y in ball c r, F y‖ ≤ ε * r ^ 2 :=
    norm_setAverage_le hballfin hballpos (fun y hy => hFbound y (ball_subset_closedBall hy))
  have hint : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g →
      IntegrableOn g (ball c r) volume := fun g hg =>
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hintE : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => y - c) (ball c r) volume :=
    ((continuous_id.sub continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  set L : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (fderiv ℝ v c) (y - c) with hL
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (1 / 2 : ℝ) * M₀ (y - c) (y - c) with hQ
  have hcont_L : Continuous L := by rw [hL]; fun_prop
  have hcont_Q : Continuous Q := by rw [hQ]; fun_prop
  have hcont_F : Continuous F := by rw [hF]; fun_prop
  have hlin : (⨍ y in ball c r, L y) = 0 := by
    have hintE0 : IntegrableOn (fun w : EuclideanSpace ℝ (Fin n) => w)
        (ball (0 : EuclideanSpace ℝ (Fin n)) r) volume :=
      (continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
        ball_subset_closedBall
    have h1 : (⨍ y in ball c r, L y)
        = ⨍ w in ball (0 : EuclideanSpace ℝ (Fin n)) r, (fderiv ℝ v c) w := by
      rw [hL]
      rw [Commons.Analysis.Measure.setAverage_ball_add c r
        (fun y => (fderiv ℝ v c) (y - c))]
      apply setAverage_congr_fun measurableSet_ball
      filter_upwards with w _
      simp only [add_sub_cancel_left]
    have h2 : (⨍ w in ball (0 : EuclideanSpace ℝ (Fin n)) r, (fderiv ℝ v c) w)
        = (fderiv ℝ v c) (⨍ w in ball (0 : EuclideanSpace ℝ (Fin n)) r, w) := by
      rw [setAverage_eq, setAverage_eq,
        ContinuousLinearMap.integral_comp_comm (fderiv ℝ v c) hintE0, map_smul]
    rw [h1, h2, setAverage_ball_self_eq_zero r, map_zero]
  have hmom : (⨍ y in ball c r, M₀ (y - c) (y - c))
      = r ^ 2 / ((n : ℝ) + 2) * Laplacian.laplacian v c := by
    rw [hΔ, Commons.Analysis.Measure.setAverage_ball_add c r (fun y => M₀ (y - c) (y - c))]
    have hcongr : (⨍ w in ball (0 : EuclideanSpace ℝ (Fin n)) r,
          M₀ ((c + w) - c) ((c + w) - c))
        = ⨍ w in ball (0 : EuclideanSpace ℝ (Fin n)) r, M₀ w w := by
      apply setAverage_congr_fun measurableSet_ball
      filter_upwards with w _
      simp only [add_sub_cancel_left]
    rw [hcongr, setAverage_ball_bilinear hnpos M₀ hrpos]
  have hquad : (⨍ y in ball c r, Q y)
      = (1 / 2) * (r ^ 2 / ((n : ℝ) + 2)) * Laplacian.laplacian v c := by
    rw [hQ, setAverage_mul_const_real, hmom]
    ring
  have havg : (⨍ y in ball c r, v y)
      = v c + (1 / 2) * (r ^ 2 / ((n : ℝ) + 2)) * Laplacian.laplacian v c
        + (⨍ y in ball c r, F y) := by
    have hcongr : (⨍ y in ball c r, v y)
        = ⨍ y in ball c r, (v c + (L y + (Q y + F y))) := by
      apply setAverage_congr_fun measurableSet_ball
      filter_upwards with y _
      simp only [hF, hL, hQ]
      ring
    rw [hcongr]
    rw [setAverage_add_real (f := fun _ : EuclideanSpace ℝ (Fin n) => v c)
        (g := fun y : EuclideanSpace ℝ (Fin n) => L y + (Q y + F y))
        (hint _ continuous_const)
        (IntegrableOn.add (hint L hcont_L) (IntegrableOn.add (hint Q hcont_Q) (hint F hcont_F)))]
    rw [setAverage_add_real (f := L) (g := fun y : EuclideanSpace ℝ (Fin n) => Q y + F y)
        (hint L hcont_L) (IntegrableOn.add (hint Q hcont_Q) (hint F hcont_F))]
    rw [setAverage_add_real (f := Q) (g := F) (hint Q hcont_Q) (hint F hcont_F)]
    rw [setAverage_const (measure_ball_pos volume c hrpos).ne' (ne_of_lt hballfin), hlin, hquad]
    ring
  have hle := h c r hrpos
  have hineq : 0 ≤ (1 / 2) * (r ^ 2 / ((n : ℝ) + 2)) * Laplacian.laplacian v c + ε * r ^ 2 := by
    have h1 : 0 ≤ (⨍ y in ball c r, v y) - v c := by linarith
    rw [havg] at h1
    have h3 : (⨍ y in ball c r, F y) ≤ ε * r ^ 2 := by
      have h4 := hFavg
      rw [Real.norm_eq_abs] at h4
      exact le_trans (le_abs_self _) h4
    linarith
  have hr2 : 0 < r ^ 2 := pow_pos hrpos 2
  have hfac : (1 / 2) * (r ^ 2 / ((n : ℝ) + 2)) * Laplacian.laplacian v c + ε * r ^ 2
      = r ^ 2 * (Laplacian.laplacian v c / (2 * ((n : ℝ) + 2)) + ε) := by
    field_simp
  rw [hfac] at hineq
  exact nonneg_of_mul_nonneg_right hineq hr2

end Commons.Analysis.Harmonic
