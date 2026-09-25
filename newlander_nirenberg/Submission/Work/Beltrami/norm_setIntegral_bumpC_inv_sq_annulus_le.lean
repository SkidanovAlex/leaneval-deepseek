import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.Wkernel
import Submission.Work.Beltrami.integral_radial_weight_inv_sq_eq_zero

namespace Work.Beltrami

open MeasureTheory Set

/-! ### Elementary measure-theoretic helpers -/

/-- A complex-valued function bounded on a finite-measure measurable set is integrable. -/
private lemma integrableOn_of_norm_le_const {s : Set ℂ} (hfin : volume s < ⊤)
    (hsm : MeasurableSet s) {F : ℂ → ℂ} (hm : AEStronglyMeasurable F (volume.restrict s))
    {M : ℝ} (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

/-- Real-valued version of `integrableOn_of_norm_le_const`. -/
private lemma integrableOn_of_bounded {s : Set ℂ} (hfin : volume s < ⊤)
    (hsm : MeasurableSet s) {F : ℂ → ℝ} (hm : AEStronglyMeasurable F (volume.restrict s))
    {M : ℝ} (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

/-- A set contained in a disc has finite volume. -/
private lemma volume_lt_top_of_subset_ball {s : Set ℂ} {c : ℂ} {R : ℝ}
    (h : s ⊆ Metric.ball c R) : volume s < ⊤ :=
  lt_of_le_of_lt (measure_mono h) (measure_ball_lt_top (x := c) (r := R))

/-- Bound for the norm of a set integral via a pointwise majorant. -/
private lemma norm_setIntegral_le_of_norm_le {s : Set ℂ} (hs : MeasurableSet s) {F : ℂ → ℂ}
    {g : ℂ → ℝ} (hg : IntegrableOn g s volume) (h : ∀ x ∈ s, ‖F x‖ ≤ g x) :
    ‖∫ x in s, F x‖ ≤ ∫ x in s, g x := by
  rw [← integral_indicator hs (f := F), ← integral_indicator hs (f := g)]
  refine norm_integral_le_of_norm_le (hg.integrable_indicator hs)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact h x hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

/-- Volume bound for the annulus `{1/2 < ‖w‖ < 1}`: its (real) volume is at most `3`
(it equals `3π/4`).  The annulus is contained in the unit disc minus the disc of radius
`1/2`, whose volumes are `π` and `π/4` by `Complex.volume_ball`. -/
private lemma volume_real_annulus_half_lt_one_le :
    volume.real {w : ℂ | (1 : ℝ) / 2 < ‖w‖ ∧ ‖w‖ < 1} ≤ 3 := by
  set T : Set ℂ := {w : ℂ | (1 : ℝ) / 2 < ‖w‖ ∧ ‖w‖ < 1} with hT
  have hdisj : Disjoint T (Metric.ball (0 : ℂ) (1 / 2)) := by
    rw [Set.disjoint_left]
    intro w hwT hwB
    rw [hT, Set.mem_ofPred_eq] at hwT
    rw [Metric.mem_ball, dist_zero_right] at hwB
    linarith [hwT.1]
  have hsubT : T ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    rw [hT, Set.mem_ofPred_eq] at hw
    rw [Metric.mem_ball, dist_zero_right]; exact hw.2
  have hsub : T ∪ Metric.ball (0 : ℂ) (1 / 2) ⊆ Metric.ball (0 : ℂ) 1 :=
    Set.union_subset hsubT (Metric.ball_subset_ball (by norm_num))
  have hTfin : volume T ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsubT)
      (measure_ball_lt_top (x := (0 : ℂ)) (r := 1)))
  have hbfin : volume (Metric.ball (0 : ℂ) (1 / 2)) ≠ ⊤ :=
    ne_of_lt (measure_ball_lt_top (x := (0 : ℂ)) (r := (1 / 2)))
  have h1 : volume T + volume (Metric.ball (0 : ℂ) (1 / 2))
      ≤ volume (Metric.ball (0 : ℂ) 1) := by
    rw [← measure_union hdisj measurableSet_ball]
    exact measure_mono hsub
  have h2 : (volume T).toReal + (volume (Metric.ball (0 : ℂ) (1 / 2))).toReal
      ≤ Real.pi := by
    rw [← ENNReal.toReal_add hTfin hbfin]
    have h3 := ENNReal.toReal_mono
      (ne_of_lt (measure_ball_lt_top (x := (0 : ℂ)) (r := 1))) h1
    rwa [show (volume (Metric.ball (0 : ℂ) 1)).toReal = Real.pi from by
      rw [Complex.volume_ball]; simp] at h3
  have hb : (volume (Metric.ball (0 : ℂ) (1 / 2))).toReal = Real.pi / 4 := by
    rw [Complex.volume_ball]; simp; ring
  show (volume T).toReal ≤ 3
  linarith [h2, hb, Real.pi_le_four]

/-- Crude uniform bound for the regularising part of the Beurling kernel over a punctured
annulus: for every `a > 0`, `‖∫_{a < ‖w‖ < 1} bumpC w * w⁻² dw‖ ≤ 12`.
Suggested route: `bumpC = 1 - (1 - bumpC)` and `1 - bumpC` vanishes on `‖w‖ ≤ 1/2`, so the
`bumpC`-integral equals `-(∫_{1/2<‖w‖<1} (1 - bumpC w) * w⁻²)`, whose norm is at most
`4 * volume{1/2 < ‖w‖ < 1} = 4 * 3π/4 = 3π < 12` because `‖w‖ ≥ 1/2` and `0 ≤ bumpC ≤ 1`;
the `∫_{a<‖w‖<1} w⁻²` term vanishes by `Work.CR.Flat.Cauchy.integral_inv_sq_annulus`. -/
theorem norm_setIntegral_bumpC_inv_sq_annulus_le {a : ℝ} (ha : 0 < a) :
    ‖∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < 1},
        (Work.Beltrami.bumpC w : ℂ) * (w ^ 2)⁻¹‖ ≤ 12 := by
  set S : Set ℂ := {w : ℂ | a < ‖w‖ ∧ ‖w‖ < 1} with hS
  set T : Set ℂ := {w : ℂ | (1 : ℝ) / 2 < ‖w‖ ∧ ‖w‖ < 1} with hT
  have hsf : ∀ w : ℂ, w ∈ S ↔ a < ‖w‖ ∧ ‖w‖ < 1 := by intro w; rw [hS]; exact Iff.rfl
  have htf : ∀ w : ℂ, w ∈ T ↔ (1 : ℝ) / 2 < ‖w‖ ∧ ‖w‖ < 1 := by
    intro w; rw [hT]; exact Iff.rfl
  have hmeasS : MeasurableSet S := by
    rw [hS]
    exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hmeasT : MeasurableSet T := by
    rw [hT]
    exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hfinS : volume S < ⊤ := by
    refine volume_lt_top_of_subset_ball (R := 1) (c := 0) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right, hsf] at *
    exact hw.2
  have hfinT : volume T < ⊤ := by
    refine volume_lt_top_of_subset_ball (R := 1) (c := 0) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right, htf] at *
    exact hw.2
  -- `w ↦ w⁻²` is integrable on the punctured annulus `S`
  have hInt : IntegrableOn (fun w : ℂ => (w ^ 2)⁻¹) S volume := by
    refine integrableOn_of_norm_le_const hfinS hmeasS ?_ (M := (a^2)⁻¹) ?_
    · exact (measurable_id.pow_const 2).inv.aestronglyMeasurable
    · intro w hw
      rw [hsf] at hw
      simp only [norm_inv, norm_pow]
      exact inv_anti₀ (by positivity) (by nlinarith [norm_nonneg w])
  -- the mean of `w⁻²` over the rotation invariant annulus `S` vanishes
  have hzero : ∫ w in S, (w ^ 2)⁻¹ = 0 := by
    have hrot : ∀ (c : Circle) (w : ℂ), w ∈ S ↔ (c : ℂ) * w ∈ S := by
      intro c w
      rw [hsf, hsf, norm_mul, Circle.norm_coe, one_mul]
    have hint : IntegrableOn
        (fun w : ℂ => (((fun _ : ℝ => (1 : ℝ)) ‖w‖ : ℝ) : ℂ) * (w ^ 2)⁻¹) S volume := by
      simpa using hInt
    have h := Work.Beltrami.integral_radial_weight_inv_sq_eq_zero (fun _ : ℝ => (1 : ℝ)) hrot hint
    simpa using h
  -- the regularised kernel `W` is bounded by `4`
  have hW4 : ∀ w : ℂ, ‖W w‖ ≤ 4 := by
    intro w
    by_cases hw : ‖w‖ ≤ 1 / 2
    · rw [W_eq_zero_of_norm_le_half hw, norm_zero]; norm_num
    · have hwpos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le (by norm_num) (le_of_lt (lt_of_not_ge hw))
      rw [W_apply, norm_mul]
      have h1 : ‖(1 : ℂ) - (bumpC w : ℂ)‖ ≤ 1 := by
        have hcast : (1 : ℂ) - (bumpC w : ℂ) = ((1 - bumpC w : ℝ) : ℂ) := by
          push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [bumpC_le_one w], by linarith [bumpC_nonneg w]⟩
      have h2 : ‖(w ^ 2)⁻¹‖ ≤ 4 := by
        rw [norm_inv, norm_pow, inv_le_comm₀ (pow_pos hwpos 2) (by norm_num : (0 : ℝ) < 4)]
        rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
        nlinarith [norm_nonneg w]
      calc ‖(1 : ℂ) - (bumpC w : ℂ)‖ * ‖(w ^ 2)⁻¹‖ ≤ 1 * 4 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
  have hvolT : volume.real T ≤ 3 := by
    rw [hT]
    exact volume_real_annulus_half_lt_one_le
  have hWbnd : ‖∫ w in S, W w‖ ≤ 4 * volume.real T := by
    have hg : IntegrableOn (fun w : ℂ => 4 * T.indicator (fun _ => (1 : ℝ)) w) S volume := by
      refine integrableOn_of_bounded hfinS hmeasS ?_ (M := 4) ?_
      · exact ((measurable_const.indicator hmeasT).const_mul 4).aestronglyMeasurable
      · intro w _
        by_cases hwt : w ∈ T
        · simp [Set.indicator_of_mem hwt]
        · simp [Set.indicator_of_notMem hwt]
    have hpt : ∀ w ∈ S, ‖W w‖ ≤ 4 * T.indicator (fun _ => (1 : ℝ)) w := by
      intro w hw
      rw [hsf] at hw
      by_cases hw2 : ‖w‖ ≤ 1 / 2
      · have hwt : w ∉ T := by rw [htf]; exact fun h => absurd h.1 (not_lt.mpr hw2)
        rw [W_eq_zero_of_norm_le_half hw2, norm_zero, Set.indicator_of_notMem hwt]
        norm_num
      · have hw2' : (1 : ℝ) / 2 < ‖w‖ := lt_of_not_ge hw2
        have hwt : w ∈ T := by rw [htf]; exact ⟨hw2', hw.2⟩
        rw [Set.indicator_of_mem hwt, mul_one]
        exact hW4 w
    have h1 := norm_setIntegral_le_of_norm_le hmeasS hg hpt
    have h2 : ∫ w in S, 4 * T.indicator (fun _ => (1 : ℝ)) w = 4 * volume.real (S ∩ T) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator hmeasT,
        MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    calc ‖∫ w in S, W w‖ ≤ ∫ w in S, 4 * T.indicator (fun _ => (1 : ℝ)) w := h1
      _ = 4 * volume.real (S ∩ T) := h2
      _ ≤ 4 * volume.real T := by
          have hm : volume.real (S ∩ T) ≤ volume.real T := by
            have h3 := ENNReal.toReal_mono (ne_of_lt hfinT)
              (measure_mono (inter_subset_right : S ∩ T ⊆ T))
            show (volume (S ∩ T)).toReal ≤ (volume T).toReal
            exact h3
          nlinarith [hm]
  have hIntW : IntegrableOn W S volume := by
    refine integrableOn_of_norm_le_const hfinS hmeasS ?_ (M := 4) ?_
    · exact W_contDiff.continuous.measurable.aestronglyMeasurable
    · intro w _; exact hW4 w
  have hdecomp : ∫ w in S, (bumpC w : ℂ) * (w ^ 2)⁻¹ = - ∫ w in S, W w := by
    have hpoint : (fun w : ℂ => (bumpC w : ℂ) * (w ^ 2)⁻¹)
        = (fun w : ℂ => (w ^ 2)⁻¹ - W w) := by
      funext w; rw [W_apply]; ring
    rw [hpoint, MeasureTheory.integral_sub hInt hIntW, hzero]
    ring
  rw [hdecomp, norm_neg]
  calc ‖∫ w in S, W w‖ ≤ 4 * volume.real T := hWbnd
    _ ≤ 4 * 3 := by nlinarith [hvolT]
    _ = 12 := by norm_num

end Work.Beltrami
