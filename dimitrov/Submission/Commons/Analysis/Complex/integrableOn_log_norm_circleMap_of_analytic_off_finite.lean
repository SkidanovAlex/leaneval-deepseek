import Mathlib
import Submission.Commons.Analysis.Complex.finite_zero_set_of_analytic_off_finset
import Submission.Commons.Analysis.Complex.analyticAt_zero_exists_lower_bound
import Submission.Commons.Analysis.Complex.circleAverage_log_norm_of_analytic_off_finite

namespace Commons.Analysis.Complex

open Set Metric Filter MeasureTheory
open scoped Topology Real

noncomputable section

theorem integrableOn_log_norm_circleMap_of_analytic_off_finite (f : ℂ → ℂ) (B : Finset ℂ)
    (hB : ∀ b ∈ B, b ∈ Metric.sphere (0 : ℂ) 1 ∧ f b ≠ 0)
    (hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    (han : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ∉ B → AnalyticAt ℂ f z)
    (hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Real.log ‖f (circleMap 0 1 θ)‖)
      (Set.Icc 0 (2 * Real.pi)) MeasureTheory.volume := by
  classical
  -- ## Step 1: the zeros of `f` on the unit circle form a finite set
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; norm_num
  have hf0 : f 0 ≠ 0 := hne 0 h0ball
  have hfin := finite_zero_set_of_analytic_off_finset f B 0 h0ball hf0 hB hcont han
  have hZfin : {z : ℂ | z ∈ Metric.sphere (0 : ℂ) 1 ∧ f z = 0}.Finite :=
    hfin.subset (fun z hz => ⟨Metric.sphere_subset_closedBall hz.1, hz.2⟩)
  let Z : Finset ℂ := hZfin.toFinset
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ Metric.sphere (0 : ℂ) 1 ∧ f z = 0 := by
    intro z; simp [Z]
  have hZnorm : ∀ z ∈ Z, ‖z‖ = 1 := by
    intro z hz
    have h := (hZmem z).mp hz
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h.1
  -- ## Step 2: local lower bounds at the zeros
  have hdata : ∀ z ∈ Z, ∃ (k : ℕ) (δ m : ℝ), 1 ≤ k ∧ 0 < δ ∧ 0 < m ∧
      ∀ w ∈ Metric.ball z δ, m * ‖w - z‖ ^ k ≤ ‖f w‖ := by
    intro z hz
    have hzsp := (hZmem z).mp hz
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hzsp.1
    have hzB : z ∉ B := fun hzB => (hB z hzB).2 hzsp.2
    exact analyticAt_zero_exists_lower_bound (han z hzcb hzB) hzsp.2
      (not_eventually_zero_at_sphere_point f B hB han hne hzsp.1)
  obtain ⟨K, D, Mlo, hK, hD, hMlo, hbnd⟩ : ∃ (K : ℂ → ℕ) (D M : ℂ → ℝ),
      (∀ z ∈ Z, 1 ≤ K z) ∧ (∀ z ∈ Z, 0 < D z) ∧ (∀ z ∈ Z, 0 < M z) ∧
      (∀ z ∈ Z, ∀ w ∈ Metric.ball z (D z), M z * ‖w - z‖ ^ K z ≤ ‖f w‖) := by
    refine ⟨fun z => if hz : z ∈ Z then Classical.choose (hdata z hz) else 0,
            fun z => if hz : z ∈ Z then Classical.choose (Classical.choose_spec (hdata z hz)) else 1,
            fun z => if hz : z ∈ Z then Classical.choose (Classical.choose_spec (Classical.choose_spec (hdata z hz))) else 1,
            ?_, ?_, ?_, ?_⟩
    · intro z hz; simp only [dif_pos hz]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).1
    · intro z hz; simp only [dif_pos hz]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.1
    · intro z hz; simp only [dif_pos hz]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.2.1
    · intro z hz; simp only [dif_pos hz]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.2.2
  -- ## Step 3: a global upper bound and a lower bound away from the zeros
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  let Mm : ℝ := max M0 1
  have hMm1 : 1 ≤ Mm := le_max_right _ _
  have hMmle : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ Mm :=
    fun w hw => le_trans (hM0 w hw) (le_max_left _ _)
  let Uball : Set ℂ := ⋃ z ∈ Z, Metric.ball z (D z)
  let Kc : Set ℂ := Metric.closedBall (0 : ℂ) 1 \ Uball
  have hKc_sub : Kc ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw; exact hw.1
  have hUball_open : IsOpen Uball := by
    simp only [Uball]; exact isOpen_biUnion (fun z _ => Metric.isOpen_ball)
  have hKc_compact : IsCompact Kc := (isCompact_closedBall (0 : ℂ) 1).diff hUball_open
  have hfnz : ∀ w ∈ Kc, f w ≠ 0 := by
    intro w hw hw0
    have hwcb : w ∈ Metric.closedBall (0 : ℂ) 1 := hKc_sub hw
    have hwsp : w ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      rw [Metric.mem_closedBall, dist_zero_right] at hwcb
      by_contra hne1
      exact hne w (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_ne hwcb hne1) hw0
    have hwZ : w ∈ Z := (hZmem w).mpr ⟨hwsp, hw0⟩
    have hmem : w ∈ Uball := by
      simp only [Uball]
      exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwZ, Metric.mem_ball_self (hD w hwZ)⟩⟩
    exact hw.2 hmem
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ Kc, m ≤ ‖f w‖ := by
    by_cases hne' : Kc.Nonempty
    · obtain ⟨x, hxKc, hxmin⟩ := hKc_compact.exists_isMinOn hne' ((hcont.mono hKc_sub).norm)
      exact ⟨‖f x‖, norm_pos_iff.mpr (hfnz x hxKc), fun w hw => hxmin hw⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne'
      exact ⟨1, one_pos, fun w hw => by rw [hne'] at hw; exact absurd hw (Set.notMem_empty w)⟩
  obtain ⟨m, hmpos, hmle⟩ := hm
  -- ## Step 4: constants and the pointwise logarithmic bound
  let Cst : ℝ := max (Real.log Mm) |Real.log m| + ∑ z ∈ Z, |Real.log (Mlo z)|
  have hsum_cst_nn : 0 ≤ ∑ z ∈ Z, |Real.log (Mlo z)| :=
    Finset.sum_nonneg (fun z _ => abs_nonneg _)
  have hmax_nonneg : 0 ≤ max (Real.log Mm) |Real.log m| :=
    le_trans (Real.log_nonneg hMm1) (le_max_left _ _)
  have hCst_nonneg : 0 ≤ Cst := by
    simp only [Cst]; linarith
  have hlogMle : Real.log Mm ≤ Cst := by
    have h1 : Real.log Mm ≤ max (Real.log Mm) |Real.log m| := le_max_left _ _
    simp only [Cst]; linarith
  have hlogmle : |Real.log m| ≤ Cst := by
    have h1 : |Real.log m| ≤ max (Real.log Mm) |Real.log m| := le_max_right _ _
    simp only [Cst]; linarith
  have hlogMlole : ∀ z ∈ Z, |Real.log (Mlo z)| ≤ Cst := by
    intro z hz
    have h1 : |Real.log (Mlo z)| ≤ ∑ w ∈ Z, |Real.log (Mlo w)| :=
      Finset.single_le_sum (f := fun w => |Real.log (Mlo w)|) (fun w _ => abs_nonneg _) hz
    simp only [Cst]; linarith
  have hbase : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      |Real.log ‖f w‖| ≤ Cst + ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| := by
    intro w hw
    have hsum_nn : 0 ≤ ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| :=
      Finset.sum_nonneg
        (fun z _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    have hlogMw : Real.log ‖f w‖ ≤ Real.log Mm :=
      log_le_log_of_le_one (norm_nonneg _) hMm1 (hMmle w hw)
    rcases em (w ∈ Uball) with hwU | hwU
    · -- `w` lies in one of the small balls around a zero
      simp only [Uball] at hwU
      rw [Set.mem_iUnion] at hwU
      obtain ⟨z0, hwU⟩ := hwU
      rw [Set.mem_iUnion] at hwU
      obtain ⟨hz0Z, hwz0⟩ := hwU
      by_cases hwz : w = z0
      · have hnn : (0 : ℝ) ≤ Cst + ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖z0 - z‖| :=
          add_nonneg hCst_nonneg
            (Finset.sum_nonneg (fun z _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
        rw [hwz, ((hZmem z0).mp hz0Z).2, norm_zero, Real.log_zero, abs_zero]
        exact hnn
      · have hwz0pos : 0 < ‖w - z0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
        have hb := hbnd z0 hz0Z w hwz0
        have hm0 : 0 < Mlo z0 := hMlo z0 hz0Z
        have hpos2 : 0 < Mlo z0 * ‖w - z0‖ ^ K z0 := by positivity
        have hlogb := Real.log_le_log hpos2 hb
        rw [Real.log_mul (ne_of_gt hm0) (pow_ne_zero _ (ne_of_gt hwz0pos)), Real.log_pow] at hlogb
        have hK0 : (0 : ℝ) ≤ (K z0 : ℝ) := Nat.cast_nonneg _
        have hterm : (K z0 : ℝ) * |Real.log ‖w - z0‖| ≤
            ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| :=
          Finset.single_le_sum (f := fun z => (K z : ℝ) * |Real.log ‖w - z‖|)
            (fun z _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) hz0Z
        have hmlo := hlogMlole z0 hz0Z
        rw [abs_le]
        constructor
        · have key : -Real.log ‖f w‖ ≤
              |Real.log (Mlo z0)| + (K z0 : ℝ) * |Real.log ‖w - z0‖| := by
            have h2 : -((K z0 : ℝ) * Real.log ‖w - z0‖) ≤
                (K z0 : ℝ) * |Real.log ‖w - z0‖| := by
              have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log ‖w - z0‖)) hK0
              simpa only [mul_neg, neg_mul] using h3
            have h4 : -(Real.log (Mlo z0)) ≤ |Real.log (Mlo z0)| := neg_le_abs _
            linarith
          linarith
        · linarith
    · -- `w` is at distance at least `D z` from every zero
      have hwKc : w ∈ Kc := ⟨hw, hwU⟩
      have hfwnz := hfnz w hwKc
      have hpos : 0 < ‖f w‖ := norm_pos_iff.mpr hfwnz
      have hml := hmle w hwKc
      have hlogm : Real.log m ≤ Real.log ‖f w‖ := Real.log_le_log hmpos hml
      rw [abs_le]
      constructor
      · have : -Real.log ‖f w‖ ≤ |Real.log m| := by
          have := neg_le_abs (Real.log m); linarith
        linarith
      · linarith
  -- ## Step 5: the dominating function is integrable on `[0, 2π]`
  let bound : ℝ → ℝ := fun θ =>
    Cst + ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|
  have hbound_int : IntegrableOn bound (Set.Icc 0 (2 * Real.pi)) volume := by
    have hsum : IntegrableOn
        (fun θ : ℝ => ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|)
        (Set.Icc 0 (2 * Real.pi)) volume := by
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)).mp ?_
      have hterm : ∀ z ∈ Z, IntervalIntegrable
          (fun θ : ℝ => (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|) volume 0 (2 * Real.pi) :=
        fun z _ => ((circleIntegrable_log_norm_sub_const (a := z) (c := 0) (r := 1)).abs).const_mul _
      have hs := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 2 * Real.pi) Z
        (f := fun z θ => (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|) hterm
      have heq : (∑ z ∈ Z, (fun θ : ℝ => (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|))
          = fun θ : ℝ => ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖| := by
        funext θ; rw [Finset.sum_apply]
      rwa [heq] at hs
    have hcst : IntegrableOn (fun _ : ℝ => Cst) (Set.Icc 0 (2 * Real.pi)) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)).mp
        (intervalIntegrable_const (c := Cst))
    have hmain : IntegrableOn
        (fun θ : ℝ => Cst + ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖circleMap 0 1 θ - z‖|)
        (Set.Icc 0 (2 * Real.pi)) volume := hcst.add hsum
    simpa only [bound] using hmain
  -- ## Step 6: conclude by dominated convergence (a.e. domination)
  have hball : ∀ θ : ℝ, circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := fun θ =>
    Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ)
  have hpt : ∀ θ : ℝ, |Real.log ‖f (circleMap 0 1 θ)‖| ≤ bound θ := by
    intro θ
    have := hbase (circleMap 0 1 θ) (hball θ)
    simpa only [bound] using this
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => Real.log ‖f (circleMap 0 1 θ)‖)
      (volume.restrict (Set.Icc 0 (2 * Real.pi))) := by
    have hcont_g : Continuous (fun θ : ℝ => f (circleMap 0 1 θ)) :=
      hcont.comp_continuous (continuous_circleMap 0 1) hball
    exact ((Real.measurable_log.comp hcont_g.norm.measurable).aestronglyMeasurable).restrict
  rw [IntegrableOn]
  refine Integrable.mono' hbound_int hmeas ?_
  filter_upwards with θ
  simpa only [Real.norm_eq_abs] using hpt θ

end

end Commons.Analysis.Complex
