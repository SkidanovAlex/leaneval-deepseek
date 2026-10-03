import Mathlib
import Submission.Work.KMTAreas.A4.kmtFhatBounded
import Submission.Work.KMTAreas.A4.lip2Projection

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open MeasureTheory Filter

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Auxiliary facts about the window symbol `winFT` -/

/-- The symbol `winFT M s` of the reproducing window is `1`-periodic in the frequency. -/
theorem winFT_add_int (M s t : ℝ) (k : ℤ) :
    winFT M s (t + (k : ℝ)) = winFT M s t := by
  show (∑' n : ℤ, lipSchChi (M * (t + (k : ℝ) - s + (n : ℝ))))
      = ∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ)))
  rw [show (∑' n : ℤ, lipSchChi (M * (t + (k : ℝ) - s + (n : ℝ))))
      = ∑' n : ℤ, (fun m : ℤ => lipSchChi (M * (t - s + (m : ℝ)))) (n + k) from
    tsum_congr fun n => by
      rw [show M * (t + (k : ℝ) - s + (n : ℝ)) = M * (t - s + ((n + k : ℤ) : ℝ)) by
        push_cast
        ring]]
  exact Function.Injective.tsum_eq (g := fun n : ℤ => n + k)
    (fun a b hab => by
      have hab' : a + k = b + k := hab
      exact (add_right_cancel_iff).mp hab')
    (f := fun m : ℤ => lipSchChi (M * (t - s + (m : ℝ)))) (fun m _ => ⟨m - k, by ring⟩)

/-- `winFT M s` is periodic of period one. -/
theorem winFT_add_one (M s t : ℝ) : winFT M s (t + 1) = winFT M s t := by
  simpa using winFT_add_int M s t 1

/-- `winFT M s` is continuous in the frequency, for `M ≠ 0`.  The sum defining it is locally
finite (only the integers `n` with `|t - s + n| < 1/|M|` contribute), so it is continuous by
`continuousOn_tsum` on a neighbourhood where the contributing `n`'s are uniformly bounded. -/
theorem continuous_winFT {M s : ℝ} (hM : M ≠ 0) : Continuous fun t : ℝ => winFT M s t := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨K, hK⟩ : ∃ K : ℤ, |t₀ - s| + 1 / |M| + 2 ≤ (K : ℝ) :=
    ⟨⌈|t₀ - s| + 1 / |M| + 2⌉, Int.le_ceil _⟩
  have hsum : Summable fun n : ℤ => (if n ∈ Finset.Icc (-K) K then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc (-K) K) fun n hn => by rw [if_neg hn]
  have hcont : ContinuousOn (fun t : ℝ => ∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ))))
      (Metric.closedBall t₀ 1) := by
    refine continuousOn_tsum (fun n => ?_) hsum (fun n x hx => ?_)
    · exact ((SchwartzMap.continuous lipSchChi).comp
        (continuous_const.mul ((continuous_id.sub continuous_const).add continuous_const))).continuousOn
    · rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] at hx
      by_cases hn : n ∈ Finset.Icc (-K) K
      · rw [if_pos hn]
        exact lipSchChi_norm_le_one _
      · rw [if_neg hn]
        have hKlt : K < |n| := by
          rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
          rcases hn with h | h
          · exact lt_of_lt_of_le (by omega : K < -n) (neg_le_abs n)
          · exact lt_of_lt_of_le h (le_abs_self n)
        have hKabs : (K : ℝ) < |((n : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast hKlt
        have hbound : 1 / |M| ≤ |x - s + (n : ℝ)| := by
          have h1 : |((n : ℤ) : ℝ)| - |x - s| ≤ |x - s + (n : ℝ)| := by
            have h := abs_add_le (x - s + (n : ℝ)) (-(x - s))
            rw [abs_neg] at h
            have hh : x - s + (n : ℝ) + -(x - s) = (n : ℝ) := by ring
            rw [hh] at h
            linarith
          have h2 : |x - s| ≤ 1 + |t₀ - s| := by
            have h := abs_add_le (x - t₀) (t₀ - s)
            have hh : x - t₀ + (t₀ - s) = x - s := by ring
            rw [hh] at h
            linarith
          linarith
        rw [winFT_term_eq_zero hM hbound]
        simp
  have hball : Metric.closedBall t₀ 1 ∈ nhds t₀ :=
    Filter.mem_of_superset (Metric.ball_mem_nhds t₀ one_pos) Metric.ball_subset_closedBall
  exact hcont.continuousAt hball

/-- A closed arc of the frequency circle is Borel measurable: it is the image of the compact
interval `[-r, r]` under the continuous map `θ ↦ α + θ`. -/
theorem measurableSet_arcSet (α : FreqCircle) (r : ℝ) : MeasurableSet (arcSet α r) := by
  have h : arcSet α r = (fun θ : ℝ => α + (((θ : ℝ)) : FreqCircle)) '' Set.Icc (-r) r := by
    ext γ
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨θ, abs_le.mp hθ, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨θ, abs_le.mpr hθ, rfl⟩
  rw [h]
  exact (isCompact_Icc.image
    (continuous_const.add (AddCircle.continuous_mk' (1 : ℝ)))).measurableSet

/-- **The mass of `𝓕_ℤ g` on a single arc is dominated by the windowed mass.**  For `M ≥ 2`,
`0 < r` and `2 M r ≤ 1`, the `L²` mass of `𝓕_ℤ g` on the arc of radius `r` around the frequency
`s` is at most the integral of `‖𝓕_ℤ g‖²` against the symbol `winFT M s` of the normalised
reproducing window of width `1/M`.  The reason is that `winFT M s = 1` on the arc of radius
`1/(2M) ⊇ arcSet s r`, while `winFT M s ≥ 0` everywhere. -/
theorem arcMass_le_windowMass (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    {M s r : ℝ} (hM : 2 ≤ M) (hr : 0 < r) (hMr : 2 * M * r ≤ 1) :
    (∫ (ξ : Work.Analysis.InverseTheory.FreqCircle) in
        Work.KMTAreas.A4.arcSet (((s : ℝ)) : Work.Analysis.InverseTheory.FreqCircle) r,
        ‖Work.Analysis.InverseTheory.ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle)
      ≤ ∫ t in (0 : ℝ)..1,
          ‖Work.Analysis.InverseTheory.ZFourier g (((t : ℝ)) : Work.Analysis.InverseTheory.FreqCircle)‖ ^ 2
            * (Work.KMTAreas.A4.winFT M s t).re := by
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hMr' : M * r ≤ 1 / 2 := by linarith
  have hvol : (AddCircle.haarAddCircle : Measure FreqCircle) = volume := by
    rw [show (volume : Measure FreqCircle) = ENNReal.ofReal 1 • AddCircle.haarAddCircle from
      AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have hSmeas : MeasurableSet (arcSet (((s : ℝ)) : FreqCircle) r) := measurableSet_arcSet _ _
  have hstep1 :
      (∫ (ξ : FreqCircle) in arcSet (((s : ℝ)) : FreqCircle) r,
          ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle)
        = ∫ a in Set.Ioc (0 : ℝ) 1,
            (arcSet (((s : ℝ)) : FreqCircle) r).indicator
              (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) (((a : ℝ)) : FreqCircle) ∂volume := by
    rw [hvol, ← MeasureTheory.integral_indicator
      (μ := (volume : Measure FreqCircle)) (s := arcSet (((s : ℝ)) : FreqCircle) r) hSmeas]
    rw [← AddCircle.integral_preimage (T := 1) (t := 0)
      (f := fun ξ : FreqCircle => (arcSet (((s : ℝ)) : FreqCircle) r).indicator
        (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) ξ)]
    simp
  have hstep2 :
      (∫ a in Set.Ioc (0 : ℝ) 1,
          ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re ∂volume)
        = ∫ t in (0 : ℝ)..1,
            ‖ZFourier g (((t : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s t).re :=
    (intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hpoint : ∀ a : ℝ,
      (arcSet (((s : ℝ)) : FreqCircle) r).indicator
          (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) (((a : ℝ)) : FreqCircle)
        ≤ ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re := by
    intro a
    by_cases hmem : (((a : ℝ)) : FreqCircle) ∈ arcSet (((s : ℝ)) : FreqCircle) r
    · rw [Set.indicator_of_mem hmem]
      obtain ⟨θ, hθ, heq⟩ := hmem
      have hper : winFT M s a = winFT M s (s + θ) := by
        have hzero : ((a - s - θ : ℝ) : FreqCircle) = 0 := by
          rw [AddCircle.coe_sub, AddCircle.coe_sub, heq]
          abel
        rw [AddCircle.coe_eq_zero_iff] at hzero
        obtain ⟨k, hk⟩ := hzero
        have hkR : (k : ℝ) = a - s - θ := by
          rw [zsmul_one] at hk
          exact hk
        have ha_eq : a = s + θ + (k : ℝ) := by linarith
        rw [ha_eq]
        exact winFT_add_int M s (s + θ) k
      have hone : winFT M s (s + θ) = 1 := by
        refine winFT_eq_one hM ?_
        rw [show (s + θ) - s = θ by ring, abs_mul, abs_of_pos hMpos]
        calc M * |θ| ≤ M * r := mul_le_mul_of_nonneg_left hθ hMpos.le
          _ ≤ 1 / 2 := hMr'
      rw [hper, hone]
      simp
    · rw [Set.indicator_of_notMem hmem]
      exact mul_nonneg (by positivity) (winFT_re_nonneg M s a)
  have hweight_int : Integrable
      (fun a : ℝ => ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    obtain ⟨C, hCpos, hCb⟩ := (kmtFhatBounded g hg).1
    have hcont : Continuous (fun a : ℝ =>
        ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re) :=
      ((((kmtFhatBounded g hg).2).norm.pow 2).congr
          (fun a => by
            show ‖Work.A3.kmtFhat g a‖ ^ 2 = ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2
            rw [kmtFhat_eq_ZFourier])).mul
        (Complex.continuous_re.comp (continuous_winFT hMne))
    refine Integrable.of_bound hcont.aestronglyMeasurable (C ^ 2) (Eventually.of_forall fun a => ?_)
    have h1 : ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 ≤ C ^ 2 := by
      have h0 : ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ≤ C := by
        rw [← kmtFhat_eq_ZFourier]
        exact hCb a
      nlinarith [norm_nonneg (ZFourier g (((a : ℝ)) : FreqCircle))]
    have h2 : |(winFT M s a).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (winFT_norm_le_one hM)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    simpa using mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hnonneg : ∀ a : ℝ, (0 : ℝ) ≤ (arcSet (((s : ℝ)) : FreqCircle) r).indicator
      (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) (((a : ℝ)) : FreqCircle) := by
    intro a
    by_cases ha : (((a : ℝ)) : FreqCircle) ∈ arcSet (((s : ℝ)) : FreqCircle) r
    · rw [Set.indicator_of_mem ha]
      positivity
    · rw [Set.indicator_of_notMem ha]
  have hmono :
      (∫ a in Set.Ioc (0 : ℝ) 1,
          (arcSet (((s : ℝ)) : FreqCircle) r).indicator
            (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) (((a : ℝ)) : FreqCircle) ∂volume)
        ≤ ∫ a in Set.Ioc (0 : ℝ) 1,
            ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re ∂volume :=
    integral_mono_of_nonneg (Eventually.of_forall hnonneg) hweight_int
      (Eventually.of_forall hpoint)
  calc (∫ (ξ : FreqCircle) in arcSet (((s : ℝ)) : FreqCircle) r,
        ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle)
      = ∫ a in Set.Ioc (0 : ℝ) 1,
          (arcSet (((s : ℝ)) : FreqCircle) r).indicator
            (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) (((a : ℝ)) : FreqCircle) ∂volume := hstep1
    _ ≤ ∫ a in Set.Ioc (0 : ℝ) 1,
          ‖ZFourier g (((a : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s a).re ∂volume := hmono
    _ = ∫ t in (0 : ℝ)..1,
          ‖ZFourier g (((t : ℝ)) : FreqCircle)‖ ^ 2 * (winFT M s t).re := hstep2

end Work.KMTAreas.A4
