import Mathlib
import Submission.Commons.Analysis.Complex.finite_zero_set_of_analytic_off_finset
import Submission.Commons.Analysis.Complex.log_norm_dist_ratio_bound
import Submission.Commons.Analysis.Complex.analyticAt_zero_exists_lower_bound

namespace Commons.Analysis.Complex

open Set Metric Filter MeasureTheory _root_.Complex
open scoped Topology Real

noncomputable section

lemma countable_preimage_circleMap_z {z : ℂ} (hz : ‖z‖ = 1) :
    {θ : ℝ | circleMap 0 1 θ = z}.Countable := by
  have hval : Complex.exp (z.arg * I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at h
    simpa using h
  refine (Set.countable_range (fun n : ℤ => z.arg + 2 * Real.pi * n)).mono ?_
  intro θ hθ
  simp only [Set.mem_ofPred_eq] at hθ
  simp only [circleMap_zero, Complex.ofReal_one, one_mul] at hθ
  rw [← hval] at hθ
  rw [Complex.exp_eq_exp_iff_exists_int] at hθ
  obtain ⟨n, hn⟩ := hθ
  refine ⟨n, ?_⟩
  have h2 : (θ : ℂ) * I = ((z.arg : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * I := by
    rw [hn]; ring
  have hmul : (θ : ℂ) = (z.arg : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) :=
    mul_right_cancel₀ Complex.I_ne_zero h2
  have hmul2 : (θ : ℂ) = ((z.arg + 2 * Real.pi * n : ℝ) : ℂ) := by
    rw [hmul]; push_cast; ring
  exact (Complex.ofReal_inj.mp hmul2).symm

lemma measure_preimage_circleMap_finset (Z : Finset ℂ) (hZ : ∀ z ∈ Z, ‖z‖ = 1) :
    volume {θ : ℝ | circleMap 0 1 θ ∈ (Z : Set ℂ)} = 0 := by
  have hcount : {θ : ℝ | circleMap 0 1 θ ∈ (Z : Set ℂ)}.Countable := by
    have hset : {θ : ℝ | circleMap 0 1 θ ∈ (Z : Set ℂ)} = ⋃ z ∈ Z, {θ : ℝ | circleMap 0 1 θ = z} := by
      ext θ; simp
    rw [hset]
    exact Set.Countable.biUnion (Z.countable_toSet) (fun z hz => countable_preimage_circleMap_z (hZ z hz))
  exact hcount.measure_zero volume

lemma log_le_log_of_le_one {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (h : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0, Real.log_zero]; exact Real.log_nonneg hy
  · exact Real.log_le_log h0 h

lemma not_eventually_zero_at_sphere_point (f : ℂ → ℂ) (B : Finset ℂ)
    (hB : ∀ b ∈ B, b ∈ Metric.sphere (0:ℂ) 1 ∧ f b ≠ 0)
    (han : ∀ z ∈ Metric.closedBall (0:ℂ) 1, z ∉ B → AnalyticAt ℂ f z)
    (hne : ∀ z ∈ Metric.ball (0:ℂ) 1, f z ≠ 0)
    {z : ℂ} (hz : z ∈ Metric.sphere (0:ℂ) 1) :
    ¬ ∀ᶠ w in nhds z, f w = 0 := by
  intro hev
  have hAnalytic : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) 1) := by
    intro w hw
    have hwcb : w ∈ Metric.closedBall (0:ℂ) 1 := Metric.ball_subset_closedBall hw
    have hwB : w ∉ B := by
      intro hwB
      have h1 := (hB w hwB).1
      rw [Metric.mem_sphere, dist_zero_right] at h1
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    exact han w hwcb hwB
  obtain ⟨N, hN, hNsub⟩ := (Filter.eventually_iff_exists_mem.mp hev)
  obtain ⟨O, hON, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hN
  have hzcl : z ∈ closure (Metric.ball (0:ℂ) 1) := by
    rw [closure_ball (0:ℂ) one_ne_zero]
    exact Metric.sphere_subset_closedBall hz
  have hinter : (O ∩ Metric.ball (0:ℂ) 1).Nonempty :=
    mem_closure_iff_nhds.mp hzcl O (hOopen.mem_nhds hzO)
  obtain ⟨z0, hz0O, hz0ball⟩ := hinter
  have hev0 : f =ᶠ[nhds z0] 0 := by
    filter_upwards [hOopen.mem_nhds hz0O] with w hw using hNsub w (hON hw)
  have hzero := hAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_ball hz0ball hev0
  exact hne 0 (by rw [Metric.mem_ball, dist_zero_right]; norm_num)
      (hzero (by rw [Metric.mem_ball, dist_zero_right]; norm_num))


theorem circleAverage_log_norm_of_analytic_off_finite (f : ℂ → ℂ) (B : Finset ℂ)
    (hB : ∀ b ∈ B, b ∈ Metric.sphere (0:ℂ) 1 ∧ f b ≠ 0)
    (hcont : ContinuousOn f (Metric.closedBall (0:ℂ) 1))
    (han : ∀ z ∈ Metric.closedBall (0:ℂ) 1, z ∉ B → AnalyticAt ℂ f z)
    (hne : ∀ z ∈ Metric.ball (0:ℂ) 1, f z ≠ 0) :
    Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 1 = Real.log ‖f 0‖ := by
  classical
  have h0ball : (0:ℂ) ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; norm_num
  have hf0 : f 0 ≠ 0 := hne 0 h0ball
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hcont
  have hfin := finite_zero_set_of_analytic_off_finset f B 0 h0ball hf0 hB hcont han
  have hZfin : {z : ℂ | z ∈ Metric.sphere (0:ℂ) 1 ∧ f z = 0}.Finite :=
    hfin.subset (fun z hz => ⟨Metric.sphere_subset_closedBall hz.1, hz.2⟩)
  let Z : Finset ℂ := hZfin.toFinset
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ Metric.sphere (0:ℂ) 1 ∧ f z = 0 := by
    intro z; simp [Z]
  have hZnorm : ∀ z ∈ Z, ‖z‖ = 1 := by
    intro z hz
    have h := (hZmem z).mp hz
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h.1
  have hdata : ∀ z ∈ Z, ∃ (k : ℕ) (δ m : ℝ), 1 ≤ k ∧ 0 < δ ∧ 0 < m ∧
      ∀ w ∈ Metric.ball z δ, m * ‖w - z‖ ^ k ≤ ‖f w‖ := by
    intro z hz
    have hzsp := (hZmem z).mp hz
    have hzcb : z ∈ Metric.closedBall (0:ℂ) 1 := Metric.sphere_subset_closedBall hzsp.1
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
    · intro z hz; simp only [dif_pos hz]; exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).1
    · intro z hz; simp only [dif_pos hz]; exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.1
    · intro z hz; simp only [dif_pos hz]; exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.2.1
    · intro z hz; simp only [dif_pos hz]; exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hdata z hz)))).2.2.2
  let Mm : ℝ := max M0 1
  have hMm1 : 1 ≤ Mm := le_max_right _ _
  have hMmle : ∀ w ∈ Metric.closedBall (0:ℂ) 1, ‖f w‖ ≤ Mm :=
    fun w hw => le_trans (hM0 w hw) (le_max_left _ _)
  let Uball : Set ℂ := ⋃ z ∈ Z, Metric.ball z (D z)
  let Kc : Set ℂ := Metric.closedBall (0:ℂ) 1 \ Uball
  have hKc_sub : Kc ⊆ Metric.closedBall (0:ℂ) 1 := by simp only [Kc]; exact Set.sdiff_subset
  have hUball_open : IsOpen Uball := by
    simp only [Uball]; exact isOpen_biUnion (fun z _ => Metric.isOpen_ball)
  have hKc_compact : IsCompact Kc := (isCompact_closedBall (0:ℂ) 1).diff hUball_open
  have hfnz : ∀ w ∈ Kc, f w ≠ 0 := by
    intro w hw hw0
    have hwcb : w ∈ Metric.closedBall (0:ℂ) 1 := hKc_sub hw
    have hwsp : w ∈ Metric.sphere (0:ℂ) 1 := by
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
  let Cst : ℝ := Real.log Mm + |Real.log m| + ∑ z ∈ Z, |Real.log (Mlo z)|
  have hCst_ge : Real.log Mm ≤ Cst := by
    simp only [Cst]; linarith [abs_nonneg (Real.log m),
      Finset.sum_nonneg (s := Z) (f := fun z => |Real.log (Mlo z)|) (fun z hz => abs_nonneg _)]
  have hsumabs_le : ∀ w : ℂ, (∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖|)
      = ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| := fun _ => rfl
  let bound : ℝ → ℝ := fun θ => Cst + ∑ z ∈ Z, (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2)
  have hbase : ∀ w ∈ Metric.closedBall (0:ℂ) 1,
      |Real.log ‖f w‖| ≤ Cst + ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| := by
    intro w hw
    have hlogMw : Real.log ‖f w‖ ≤ Real.log Mm := log_le_log_of_le_one (norm_nonneg _) hMm1 (hMmle w hw)
    have hsum_nn : 0 ≤ ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| :=
      Finset.sum_nonneg (s := Z) (f := fun z => (K z : ℝ) * |Real.log ‖w - z‖|) (fun z hz => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    rcases em (w ∈ Uball) with hwU | hwU
    · simp only [Uball] at hwU
      rw [Set.mem_iUnion] at hwU
      obtain ⟨z0, hwU⟩ := hwU
      rw [Set.mem_iUnion] at hwU
      obtain ⟨hz0Z, hwz0⟩ := hwU
      have hb := hbnd z0 hz0Z w hwz0
      have hMloh : 0 < Mlo z0 := hMlo z0 hz0Z
      have hle1 : |Real.log (Mlo z0)| ≤ Cst := by
        simp only [Cst]
        have : |Real.log (Mlo z0)| ≤ ∑ z ∈ Z, |Real.log (Mlo z)| :=
          Finset.single_le_sum (f := fun z => |Real.log (Mlo z)|) (fun z hz => abs_nonneg _) hz0Z
        linarith [abs_nonneg (Real.log m), Real.log_nonneg hMm1]
      have hle2 : (K z0 : ℝ) * |Real.log ‖w - z0‖| ≤
          ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖w - z‖| :=
        Finset.single_le_sum (f := fun z => (K z : ℝ) * |Real.log ‖w - z‖|)
          (fun z hz => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) hz0Z
      have hneg : -Real.log ‖f w‖ ≤ |Real.log (Mlo z0)| + (K z0 : ℝ) * |Real.log ‖w - z0‖| := by
        rcases eq_or_lt_of_le (norm_nonneg (f w)) with h0 | hpos
        · rw [← h0, Real.log_zero, neg_zero]; positivity
        · have hwnz : w ≠ z0 := by
            intro hh
            rw [hh, ((hZmem z0).mp hz0Z).2, norm_zero] at hpos
            exact lt_irrefl 0 hpos
          have hwz0pos : 0 < ‖w - z0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwnz)
          have hpos2 : 0 < Mlo z0 * ‖w - z0‖ ^ K z0 := by positivity
          have hlogb := Real.log_le_log hpos2 hb
          rw [Real.log_mul (ne_of_gt hMloh) (pow_ne_zero _ (ne_of_gt hwz0pos)), Real.log_pow] at hlogb
          have h2 : -((K z0 : ℝ) * Real.log ‖w - z0‖) ≤ (K z0 : ℝ) * |Real.log ‖w - z0‖| := by
            have := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log ‖w - z0‖)) (Nat.cast_nonneg (K z0))
            simpa only [mul_neg] using this
          have h3 : -(Real.log (Mlo z0)) ≤ |Real.log (Mlo z0)| := neg_le_abs _
          linarith
      rw [abs_le]
      exact ⟨by linarith [hneg, hle1, hle2], by linarith [hlogMw, hCst_ge, hsum_nn]⟩
    · have hwKc : w ∈ Kc := ⟨hw, hwU⟩
      have hfwnz := hfnz w hwKc
      have hpos : 0 < ‖f w‖ := norm_pos_iff.mpr hfwnz
      have hml := hmle w hwKc
      have hlogmle : Real.log m ≤ Real.log ‖f w‖ := Real.log_le_log hmpos hml
      have hle3 : |Real.log m| ≤ Cst := by
        simp only [Cst]
        linarith [Finset.sum_nonneg (s := Z) (f := fun z => |Real.log (Mlo z)|) (fun z hz => abs_nonneg _), Real.log_nonneg hMm1]
      rw [abs_le]
      exact ⟨by linarith [hlogmle, hle3, hsum_nn, neg_le_abs (Real.log m)], by linarith [hlogMw, hCst_ge, hsum_nn]⟩
  have hevIoo : ∀ᶠ r in 𝓝[<] (1:ℝ), r ∈ Ioo (1/2 : ℝ) 1 := by
    have h1 : Ioi (1/2 : ℝ) ∈ 𝓝[<] (1:ℝ) :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds (by norm_num))
    have h2 : Iio (1 : ℝ) ∈ 𝓝[<] (1:ℝ) := self_mem_nhdsWithin
    filter_upwards [h1, h2] with r hr1 hr2
    exact ⟨hr1, hr2⟩
  have hbad_null : ∀ᵐ θ ∂(volume : Measure ℝ), circleMap 0 1 θ ∉ (Z : Set ℂ) := by
    rw [MeasureTheory.ae_iff]
    have : {a : ℝ | ¬ (circleMap 0 1 a ∉ (Z : Set ℂ))} = {θ : ℝ | circleMap 0 1 θ ∈ (Z : Set ℂ)} := by
      ext a; simp
    rw [this]
    exact measure_preimage_circleMap_finset Z hZnorm
  have hbound_int : IntervalIntegrable bound volume 0 (2 * Real.pi) := by
    have h1 : IntervalIntegrable (fun _ : ℝ => Cst) volume 0 (2 * Real.pi) := intervalIntegrable_const
    have h2 : IntervalIntegrable
        (fun θ : ℝ => ∑ z ∈ Z, (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2))
        volume 0 (2 * Real.pi) := by
      have hs := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 2 * Real.pi) Z
        (f := fun z θ => (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2)) (fun z hz => ?_)
      · have heq : (∑ z ∈ Z, (fun θ : ℝ => (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2)))
            = fun θ : ℝ => ∑ z ∈ Z, (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2) := by
          funext θ; rw [Finset.sum_apply]
        rw [heq] at hs; exact hs
      · refine IntervalIntegrable.const_mul ?_ _
        exact IntervalIntegrable.add ((circleIntegrable_log_norm_sub_const (a := z) (c := 0) (1)).abs) intervalIntegrable_const
    exact h1.add h2
  have hF_meas : ∀ᶠ r in 𝓝[<] (1:ℝ),
      AEStronglyMeasurable (fun θ : ℝ => Real.log ‖f (circleMap 0 r θ)‖)
        (volume.restrict (uIoc 0 (2 * Real.pi))) := by
    filter_upwards [hevIoo] with r hr
    have hrball : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
      intro θ
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (by linarith [hr.1] : 0 < r)]
      exact hr.2
    have hcf : Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := by
      have hcm : Continuous (fun θ : ℝ => circleMap 0 r θ) := by fun_prop [circleMap]
      exact (hcont.mono Metric.ball_subset_closedBall).comp_continuous hcm (fun θ => hrball θ)
    have hlog : Continuous (fun θ : ℝ => Real.log ‖f (circleMap 0 r θ)‖) := by
      rw [continuous_iff_continuousAt]
      intro θ
      have hne' : ‖f (circleMap 0 r θ)‖ ≠ 0 := norm_ne_zero_iff.mpr (hne _ (hrball θ))
      have h1 : ContinuousAt (fun y : ℂ => Real.log ‖y‖) (f (circleMap 0 r θ)) :=
        (Real.continuousAt_log hne').comp continuous_norm.continuousAt
      exact ContinuousAt.comp (x := θ) h1 hcf.continuousAt
    exact hlog.aestronglyMeasurable.restrict
  have h_bound : ∀ᶠ r in 𝓝[<] (1:ℝ), ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ uIoc 0 (2 * Real.pi) → |Real.log ‖f (circleMap 0 r θ)‖| ≤ bound θ := by
    filter_upwards [hevIoo] with r hr
    filter_upwards [hbad_null] with θ hθbad hθmem
    have hrle : r ≤ 1 := le_of_lt hr.2
    have hrge : 1/2 ≤ r := le_of_lt hr.1
    have hwcb : circleMap 0 r θ ∈ Metric.closedBall (0:ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos (by linarith [hr.1] : 0 < r)]
      exact hrle
    have hb := hbase _ hwcb
    have hsumle : ∑ z ∈ Z, (K z : ℝ) * |Real.log ‖circleMap 0 r θ - z‖| ≤
        ∑ z ∈ Z, (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2) := by
      apply Finset.sum_le_sum
      intro z hz
      have hz1 : ‖z‖ = 1 := hZnorm z hz
      have hne_ : circleMap 0 1 θ ≠ z := fun hh => hθbad (by rw [hh]; exact hz)
      have hgeo := log_norm_dist_ratio_bound hz1 hrge hrle hne_
      have hKnn : (0:ℝ) ≤ K z := Nat.cast_nonneg _
      nlinarith [hgeo, hKnn]
    have : bound θ = Cst + ∑ z ∈ Z, (K z : ℝ) * (|Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2) := rfl
    rw [this]
    linarith
  have h_lim : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ uIoc 0 (2 * Real.pi) →
      Tendsto (fun r : ℝ => Real.log ‖f (circleMap 0 r θ)‖) (𝓝[<] (1:ℝ))
        (𝓝 (Real.log ‖f (circleMap 0 1 θ)‖)) := by
    filter_upwards [hbad_null] with θ hθbad hθmem
    have hne0 : f (circleMap 0 1 θ) ≠ 0 := by
      intro h0
      exact hθbad (by
        rw [Finset.mem_coe, hZmem]
        exact ⟨by rw [Metric.mem_sphere, dist_zero_right, norm_circleMap_zero, abs_one], h0⟩)
    have hpath : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] (1:ℝ))
        (𝓝 (circleMap 0 1 θ)) := by
      have hc : Continuous (fun r : ℝ => circleMap 0 r θ) := by
        simp only [circleMap]; fun_prop
      exact hc.continuousAt.mono_left inf_le_left
    have hg : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] (1:ℝ))
        (𝓝[Metric.closedBall (0:ℂ) 1] (circleMap 0 1 θ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hpath, ?_⟩
      filter_upwards [hevIoo] with r hr
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg (le_of_lt (by linarith [hr.1] : (0:ℝ) < r))]
      exact le_of_lt hr.2
    have hfcont : ContinuousWithinAt f (Metric.closedBall (0:ℂ) 1) (circleMap 0 1 θ) :=
      hcont.continuousWithinAt (by rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one])
    have hcircle : Tendsto (fun r : ℝ => f (circleMap 0 r θ)) (𝓝[<] (1:ℝ))
        (𝓝 (f (circleMap 0 1 θ))) := hfcont.tendsto.comp hg
    have hlogc : ContinuousAt (fun y : ℂ => Real.log ‖y‖) (f (circleMap 0 1 θ)) :=
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hne0)).comp continuous_norm.continuousAt
    exact hlogc.tendsto.comp hcircle
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝[<] (1:ℝ)) (a := 0) (b := 2 * Real.pi)
      (F := fun r θ => Real.log ‖f (circleMap 0 r θ)‖)
      (f := fun θ => Real.log ‖f (circleMap 0 1 θ)‖)
      (bound := bound) hF_meas h_bound hbound_int h_lim
  have hconv : Tendsto (fun r : ℝ => Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 r)
      (𝓝[<] (1:ℝ)) (𝓝 (Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 1)) := by
    have h2 := hDCT.const_smul ((2 * Real.pi)⁻¹)
    simpa only [Real.circleAverage_def, smul_eq_mul] using h2
  have hconst : Tendsto (fun r : ℝ => Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 r)
      (𝓝[<] (1:ℝ)) (𝓝 (Real.log ‖f 0‖)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hevIoo] with r hr
    have hrpos : 0 < r := by linarith [hr.1]
    have hharm : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖f z‖) (Metric.closedBall (0:ℂ) |r|) := by
      rw [abs_of_pos hrpos]
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      have hzball : z ∈ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hz hr.2
      have hzB : z ∉ B := by
        intro hzB
        have h1 := (hB z hzB).1
        rw [Metric.mem_sphere, dist_zero_right] at h1
        rw [Metric.mem_ball, dist_zero_right] at hzball
        linarith
      exact AnalyticAt.harmonicAt_log_norm (han z (Metric.ball_subset_closedBall hzball) hzB) (hne z hzball)
    have hmean : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 r = Real.log ‖f 0‖ :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm
    exact hmean.symm
  exact tendsto_nhds_unique hconv hconst

end

end Commons.Analysis.Complex
