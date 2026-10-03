import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.CircleSubMeanValue

/-!
# Maximum principle without continuity

The main result of this file, `Work.SimplyConnected.ABS.lsc_le_of_circleSubMeanValue`, is the
maximum principle for *lower* semicontinuous functions satisfying the circle sub-mean-value
inequality, on a relatively compact open set of a Riemann surface.

Strategy: the upper semicontinuous envelope `uscEnv U w` of `w` (the limsup of `w` along the trace
filter of `U`) dominates `w`, is upper semicontinuous, and inherits the circle sub-mean-value
inequality (this is the "the circle average of an upper semicontinuous function is upper
semicontinuous" fact together with monotonicity of the average).  The upper semicontinuous maximum
principle `usc_le_of_circleSubMeanValue` then applies to the envelope.
-/

open Filter Set MeasureTheory Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*}

section Envelope

variable [TopologicalSpace X]

/-- **The upper semicontinuous envelope of `w` along the trace filter of `U`.**  This is the
infimum of the eventual upper bounds of `w` near `x` (within `U`); it equals the `limsup` of `w`
along `𝓝[U] x`. -/
noncomputable def uscEnv (U : Set X) (w : X → ℝ) (x : X) : ℝ :=
  sInf {t : ℝ | ∀ᶠ y in 𝓝[U] x, w y ≤ t}

theorem uscEnv_eq_limsup (U : Set X) (w : X → ℝ) (x : X) :
    uscEnv U w x = Filter.limsup w (𝓝[U] x) := by
  rw [uscEnv, Filter.limsup, Filter.limsSup]
  rfl

/-- The set of eventual upper bounds of `w` is bounded below as soon as `w` is eventually bounded
below and the trace filter is proper. -/
theorem bddBelow_eventualUpperBounds {U : Set X} {w : X → ℝ} {x : X} {m : ℝ}
    (hne : (𝓝[U] x).NeBot) (hm : ∀ᶠ y in 𝓝[U] x, m ≤ w y) :
    BddBelow {t : ℝ | ∀ᶠ y in 𝓝[U] x, w y ≤ t} := by
  refine ⟨m, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  have h3 : ∀ᶠ y in 𝓝[U] x, False := by
    filter_upwards [ht, hm] with y hy1 hy2
    exact absurd hy1 (not_le.mpr (lt_of_lt_of_le hlt hy2))
  exact hne.ne ((Filter.eventually_false_iff_eq_bot).mp h3)

/-- An eventual upper bound of `w` bounds the envelope from above. -/
theorem uscEnv_le_of_eventually {U : Set X} {w : X → ℝ} {x : X} {m t : ℝ}
    (hne : (𝓝[U] x).NeBot) (hm : ∀ᶠ y in 𝓝[U] x, m ≤ w y)
    (ht : ∀ᶠ y in 𝓝[U] x, w y ≤ t) : uscEnv U w x ≤ t := by
  rw [uscEnv]
  exact csInf_le (bddBelow_eventualUpperBounds hne hm) ht

/-- Any number strictly above the envelope is an eventual upper bound. -/
theorem eventually_le_of_lt_uscEnv {U : Set X} {w : X → ℝ} {x : X} {t : ℝ}
    (hne : (𝓝[U] x).NeBot) (hK : ∃ b, ∀ᶠ y in 𝓝[U] x, w y ≤ b)
    (ht : uscEnv U w x < t) : ∀ᶠ y in 𝓝[U] x, w y ≤ t := by
  by_contra hcon
  rw [not_eventually] at hcon
  have hcon' : ∃ᶠ y in 𝓝[U] x, t < w y := by simpa only [not_le] using hcon
  have hlt : t ≤ uscEnv U w x := by
    rw [uscEnv]
    refine le_csInf hK ?_
    intro s hs
    by_contra hcon2
    push Not at hcon2
    obtain ⟨y, hy1, hy2⟩ := (hcon'.and_eventually hs).exists
    exact absurd hy2 (not_le.mpr (lt_trans hcon2 hy1))
  exact absurd hlt (not_le.mpr ht)

/-- The envelope dominates `w` at points where `w` is lower semicontinuous. -/
theorem le_uscEnv {U : Set X} {w : X → ℝ} {x : X}
    (hne : (𝓝[U] x).NeBot) (hK : ∃ b, ∀ᶠ y in 𝓝[U] x, w y ≤ b)
    (hlsc : ∀ t : ℝ, t < w x → ∀ᶠ y in 𝓝[U] x, t < w y) :
    w x ≤ uscEnv U w x := by
  rw [uscEnv]
  refine le_csInf hK ?_
  intro t ht
  by_contra hcon
  push Not at hcon
  have h3 : ∀ᶠ y in 𝓝[U] x, False := by
    filter_upwards [ht, hlsc t hcon] with y hy1 hy2
    exact absurd hy1 (not_le.mpr hy2)
  exact hne.ne ((Filter.eventually_false_iff_eq_bot).mp h3)

/-- Values of `w` close to the envelope occur frequently. -/
theorem frequently_lt_of_lt_uscEnv {U : Set X} {w : X → ℝ} {x : X} {m t : ℝ}
    (hne : (𝓝[U] x).NeBot) (hm : ∀ᶠ y in 𝓝[U] x, m ≤ w y)
    (hK : ∃ b, ∀ᶠ y in 𝓝[U] x, w y ≤ b)
    (ht : t < uscEnv U w x) : ∃ᶠ y in 𝓝[U] x, t < w y := by
  by_contra hcon
  rw [not_frequently] at hcon
  have hcon' : ∀ᶠ y in 𝓝[U] x, w y ≤ t := by simpa only [not_lt] using hcon
  exact absurd (uscEnv_le_of_eventually hne hm hcon') (not_le.mpr ht)

/-- Monotonicity of the envelope in the function. -/
theorem uscEnv_mono {U : Set X} {w w' : X → ℝ} {x : X} {m : ℝ}
    (hne : (𝓝[U] x).NeBot) (hm : ∀ᶠ y in 𝓝[U] x, m ≤ w y)
    (hK : ∃ b, ∀ᶠ y in 𝓝[U] x, w' y ≤ b)
    (hww : ∀ᶠ y in 𝓝[U] x, w y ≤ w' y) : uscEnv U w x ≤ uscEnv U w' x := by
  rw [uscEnv, uscEnv]
  refine csInf_le_csInf (bddBelow_eventualUpperBounds hne hm) hK ?_
  intro t ht
  filter_upwards [ht, hww] with y hy1 hy2
  exact le_trans hy2 hy1

/-- **The envelope is upper semicontinuous** on an open set where `w` is lower semicontinuous and
bounded above. -/
theorem uscEnv_upperSemicontinuousOn {U : Set X} (hU : IsOpen U) {w : X → ℝ} {K : ℝ}
    (hK : ∀ x ∈ U, w x ≤ K) (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x) :
    UpperSemicontinuousOn (uscEnv U w) U := by
  intro x hx t ht
  obtain ⟨ε, hε, hεt⟩ : ∃ ε : ℝ, 0 < ε ∧ uscEnv U w x + ε < t :=
    ⟨(t - uscEnv U w x) / 2, by linarith, by linarith⟩
  have hne : (𝓝[U] x).NeBot :=
    (mem_closure_iff_nhdsWithin_neBot).mp (subset_closure hx)
  have hKx : ∃ b, ∀ᶠ z in 𝓝[U] x, w z ≤ b :=
    ⟨K, mem_nhdsWithin_of_mem_nhds (by
      filter_upwards [hU.mem_nhds hx] with z hz using hK z hz)⟩
  have hmem : ∀ᶠ y in 𝓝[U] x, w y ≤ uscEnv U w x + ε :=
    eventually_le_of_lt_uscEnv hne hKx (by linarith)
  have hset : {y : X | w y ≤ uscEnv U w x + ε} ∈ 𝓝[U] x := hmem
  rw [mem_nhdsWithin] at hset
  obtain ⟨V, hVopen, hxV, hVsub⟩ := hset
  refine Filter.mem_of_superset (show V ∩ U ∈ 𝓝[U] x from
    inter_mem (mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hxV)) self_mem_nhdsWithin) ?_
  intro y hy
  have hyU : y ∈ U := hy.2
  have hney : (𝓝[U] y).NeBot :=
    (mem_closure_iff_nhdsWithin_neBot).mp (subset_closure hyU)
  have hlow : ∀ᶠ z in 𝓝[U] y, w y - 1 ≤ w z := by
    have h1 : ∀ᶠ z in 𝓝 y, w y - 1 < w z := hlsc y hyU (w y - 1) (by linarith)
    filter_upwards [mem_nhdsWithin_of_mem_nhds h1] with z hz
    exact le_of_lt hz
  have hup : ∀ᶠ z in 𝓝[U] y, w z ≤ uscEnv U w x + ε := by
    refine Filter.mem_of_superset (show V ∩ U ∈ 𝓝[U] y from
      inter_mem (mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hy.1)) self_mem_nhdsWithin) ?_
    intro z hz
    exact hVsub ⟨hz.1, hz.2⟩
  calc uscEnv U w y ≤ uscEnv U w x + ε := uscEnv_le_of_eventually hney hlow hup
    _ < t := hεt

end Envelope


section Plane

theorem circleIntegrable_of_bound {f : ℂ → ℝ} {c : ℂ} {R C : ℝ}
    (hf : Measurable fun θ : ℝ => f (circleMap c R θ))
    (hC : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ C) :
    CircleIntegrable f c R := by
  rw [circleIntegrable_def, intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ hf.aestronglyMeasurable.restrict C ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · refine Eventually.of_forall fun θ => ?_
    exact hC _ (circleMap_mem_sphere' c R θ)

/-- Measurability of the pullback of an upper semicontinuous function. -/
theorem measurable_circleMap_comp_of_upperSemicontinuousOn {f : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (husc : UpperSemicontinuousOn f (Metric.closedBall z |R|)) :
    Measurable fun θ : ℝ => f (circleMap z R θ) := by
  refine measurable_of_Iio (fun a => ?_)
  obtain ⟨u, huopen, hu⟩ := (upperSemicontinuousOn_iff_preimage_Iio.mp husc) a
  have hset : (fun θ : ℝ => f (circleMap z R θ)) ⁻¹' Set.Iio a = (circleMap z R) ⁻¹' u := by
    ext θ
    have h1 : circleMap z R θ ∈ Metric.closedBall z |R| :=
      Metric.sphere_subset_closedBall (circleMap_mem_sphere' z R θ)
    constructor
    · intro h
      have hmem : circleMap z R θ ∈ Metric.closedBall z |R| ∩ f ⁻¹' Set.Iio a := ⟨h1, h⟩
      rw [hu] at hmem
      exact hmem.2
    · intro h
      have hmem : circleMap z R θ ∈ Metric.closedBall z |R| ∩ u := ⟨h1, h⟩
      rw [← hu] at hmem
      exact hmem.2
  rw [hset]
  exact (huopen.preimage (continuous_circleMap z R)).measurableSet

theorem measurable_circleMap_comp_of_lowerSemicontinuousOn {f : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (hlsc : LowerSemicontinuousOn f (Metric.closedBall z |R|)) :
    Measurable fun θ : ℝ => f (circleMap z R θ) := by
  refine measurable_of_Ioi (fun a => ?_)
  obtain ⟨u, huopen, hu⟩ := (lowerSemicontinuousOn_iff_preimage_Ioi.mp hlsc) a
  have hset : (fun θ : ℝ => f (circleMap z R θ)) ⁻¹' Set.Ioi a = (circleMap z R) ⁻¹' u := by
    ext θ
    have h1 : circleMap z R θ ∈ Metric.closedBall z |R| :=
      Metric.sphere_subset_closedBall (circleMap_mem_sphere' z R θ)
    constructor
    · intro h
      have hmem : circleMap z R θ ∈ Metric.closedBall z |R| ∩ f ⁻¹' Set.Ioi a := ⟨h1, h⟩
      rw [hu] at hmem
      exact hmem.2
    · intro h
      have hmem : circleMap z R θ ∈ Metric.closedBall z |R| ∩ u := ⟨h1, h⟩
      rw [← hu] at hmem
      exact hmem.2
  rw [hset]
  exact (huopen.preimage (continuous_circleMap z R)).measurableSet

theorem eq_empty_of_isOpen_of_measure_zero {U : Set ℝ} (hU : IsOpen U) (h0 : volume U = 0) :
    U = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  have hpos : 0 < volume (Metric.ball x ε) := measure_ball_pos volume x hε
  have hle : volume (Metric.ball x ε) ≤ volume U := measure_mono hεU
  rw [h0] at hle
  exact absurd hle (not_le.mpr hpos)

/-- **If a nonnegative lower semicontinuous function on a circle has vanishing average, it
vanishes identically on that circle.** -/
theorem eq_zero_on_sphere_of_circleAverage_eq_zero_of_lowerSemicontinuous {D : ℂ → ℝ} {c : ℂ}
    {r C : ℝ} (hr : 0 < r) (hlsc : LowerSemicontinuousOn D (Metric.closedBall c |r|))
    (hnonneg : ∀ x ∈ Metric.sphere c |r|, 0 ≤ D x)
    (hC : ∀ x ∈ Metric.sphere c |r|, D x ≤ C)
    (havg : Real.circleAverage D c r = 0) :
    ∀ x ∈ Metric.sphere c |r|, D x = 0 := by
  set G : ℝ → ℝ := fun τ => D (circleMap c r τ) with hGdef
  have hGmeas : Measurable G := measurable_circleMap_comp_of_lowerSemicontinuousOn hlsc
  have hGnn : ∀ τ, 0 ≤ G τ := fun τ => hnonneg _ (circleMap_mem_sphere' c r τ)
  have hbdd : ∀ x ∈ Metric.sphere c |r|, ‖D x‖ ≤ max |C| 0 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x hx)]
    exact le_trans (hC x hx) (le_trans (le_abs_self C) (le_max_left _ _))
  have hint : Integrable G (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable (max |C| 0) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with τ hτ
    exact hbdd _ (circleMap_mem_sphere' c r τ)
  have hGi : ∫ τ in 0..2 * Real.pi, G τ = 0 := by
    have h2 := havg
    rw [Real.circleAverage_def] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))
    · exact h
  have hae : G =ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp ?_
    · exact Eventually.of_forall hGnn
    · rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
      exact hGi
  have hopen : IsOpen {τ : ℝ | G τ ≠ 0} := by
    obtain ⟨u, huopen, hu⟩ := (lowerSemicontinuousOn_iff_preimage_Ioi.mp hlsc) 0
    have hset : {τ : ℝ | G τ ≠ 0} = (circleMap c r) ⁻¹' u := by
      ext τ
      have h1 : circleMap c r τ ∈ Metric.closedBall c |r| :=
        Metric.sphere_subset_closedBall (circleMap_mem_sphere' c r τ)
      constructor
      · intro h
        have h' : 0 < D (circleMap c r τ) := lt_of_le_of_ne (hGnn τ) (Ne.symm h)
        have hmem : circleMap c r τ ∈ Metric.closedBall c |r| ∩ D ⁻¹' Set.Ioi 0 := ⟨h1, h'⟩
        rw [hu] at hmem
        exact hmem.2
      · intro h
        have hmem : circleMap c r τ ∈ Metric.closedBall c |r| ∩ u := ⟨h1, h⟩
        rw [← hu] at hmem
        have : 0 < D (circleMap c r τ) := hmem.2
        simp only [hGdef]
        exact ne_of_gt this
    rw [hset]
    exact huopen.preimage (continuous_circleMap c r)
  have hnull : volume ({τ : ℝ | G τ ≠ 0} ∩ Set.Ioo 0 (2 * Real.pi)) = 0 := by
    have h := MeasureTheory.ae_iff.mp (show ∀ᵐ τ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))),
        G τ = 0 from hae)
    have h' : volume ({τ : ℝ | G τ ≠ 0} ∩ Set.Ioc 0 (2 * Real.pi)) = 0 := by
      have h2 := MeasureTheory.Measure.restrict_apply (μ := volume)
        (s := Set.Ioc 0 (2 * Real.pi)) (t := {τ : ℝ | G τ ≠ 0})
        ((hGmeas (measurableSet_singleton 0)).compl)
      rw [h2] at h
      exact h
    refine measure_mono_null ?_ h'
    intro τ hτ
    exact ⟨hτ.1, hτ.2.1, le_of_lt hτ.2.2⟩
  have hemp : {τ : ℝ | G τ ≠ 0} ∩ Set.Ioo 0 (2 * Real.pi) = ∅ :=
    eq_empty_of_isOpen_of_measure_zero (hopen.inter isOpen_Ioo) hnull
  have hIoo : ∀ τ ∈ Set.Ioo 0 (2 * Real.pi), G τ = 0 := by
    intro τ hτ
    by_contra hcon
    have hmem : τ ∈ {τ : ℝ | G τ ≠ 0} ∩ Set.Ioo 0 (2 * Real.pi) := ⟨hcon, hτ⟩
    rw [hemp] at hmem
    exact hmem
  -- endpoints
  have h0 : G 0 = 0 := by
    by_contra hcon
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hopen 0 hcon
    have h1 : 0 < min ε (2 * Real.pi) := lt_min hε (by positivity)
    have he1 : 0 < min ε (2 * Real.pi) / 2 := half_pos h1
    have he2 : min ε (2 * Real.pi) / 2 < ε :=
      lt_of_lt_of_le (half_lt_self h1) (min_le_left _ _)
    have he3 : min ε (2 * Real.pi) / 2 < 2 * Real.pi :=
      lt_of_lt_of_le (half_lt_self h1) (min_le_right _ _)
    have hmem : min ε (2 * Real.pi) / 2 ∈ {τ : ℝ | G τ ≠ 0} :=
      hεU (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he1]; exact he2)
    have hmem2 : min ε (2 * Real.pi) / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨he1, he3⟩
    have hne : G (min ε (2 * Real.pi) / 2) ≠ 0 := hmem
    rw [hIoo _ hmem2] at hne
    exact hne rfl
  have h2pi : G (2 * Real.pi) = 0 := by
    by_contra hcon
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hopen (2 * Real.pi) hcon
    have h1 : 0 < min ε (2 * Real.pi) := lt_min hε (by positivity)
    have he1 : 0 < min ε (2 * Real.pi) / 2 := half_pos h1
    have he2 : min ε (2 * Real.pi) / 2 < ε :=
      lt_of_lt_of_le (half_lt_self h1) (min_le_left _ _)
    have he3 : min ε (2 * Real.pi) / 2 < 2 * Real.pi :=
      lt_of_lt_of_le (half_lt_self h1) (min_le_right _ _)
    have hmem : 2 * Real.pi - min ε (2 * Real.pi) / 2 ∈ {τ : ℝ | G τ ≠ 0} := by
      refine hεU ?_
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show (2 * Real.pi - min ε (2 * Real.pi) / 2) - 2 * Real.pi
          = -(min ε (2 * Real.pi) / 2) by ring, abs_neg, abs_of_pos he1]
      exact he2
    have hmem2 : 2 * Real.pi - min ε (2 * Real.pi) / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) :=
      ⟨by linarith, by linarith⟩
    have hne : G (2 * Real.pi - min ε (2 * Real.pi) / 2) ≠ 0 := hmem
    rw [hIoo _ hmem2] at hne
    exact hne rfl
  intro x hx
  rw [← image_circleMap_Ioc c r] at hx
  obtain ⟨τ, hτ, rfl⟩ := hx
  rcases lt_or_eq_of_le hτ.2 with hlt | heq
  · exact hIoo τ ⟨hτ.1, hlt⟩
  · rw [heq]; exact h2pi


/-- **Strong maximum principle (plane, upper semicontinuous version).**  If `f` is upper
semicontinuous and bounded on the closed ball `closedBall z ρ`, satisfies the circle
sub-mean-value inequality on the open ball, and attains its maximum `M` at the centre, then `f ≡ M`
on the open ball.

The proof passes to the deficit `D = M - f`, which is lower semicontinuous, nonnegative with
`D z = 0` and satisfies the *reverse* circle mean-value inequality `⨍ D ≤ D`; the set `{D = 0}` is
then clopen in the ball (closed by lower semicontinuity, open by the circle lemma above), hence
all of the ball. -/
theorem eqOn_ball_of_isMaxOn_of_upperSemicontinuous {f : ℂ → ℝ} {z : ℂ} {ρ M m : ℝ} (hρ : 0 < ρ)
    (husc : UpperSemicontinuousOn f (Metric.closedBall z ρ))
    (hm : ∀ w ∈ Metric.closedBall z ρ, m ≤ f w)
    (hM : ∀ w ∈ Metric.closedBall z ρ, f w ≤ M) (hMz : f z = M)
    (hmvi : ∀ p ∈ Metric.ball z ρ, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball z ρ →
        f p ≤ Real.circleAverage f p r) :
    ∀ w ∈ Metric.ball z ρ, f w = M := by
  set D : ℂ → ℝ := fun x => M - f x with hDdef
  have hDlsc : LowerSemicontinuousOn D (Metric.closedBall z ρ) := by
    have h1 : LowerSemicontinuousOn (fun x : ℂ => -f x) (Metric.closedBall z ρ) := husc.neg
    have h2 : LowerSemicontinuousOn (fun _ : ℂ => M) (Metric.closedBall z ρ) :=
      continuousOn_const.lowerSemicontinuousOn
    have := h1.add h2
    simpa [hDdef, sub_eq_add_neg, add_comm] using this
  have hDbdd : ∀ x ∈ Metric.closedBall z ρ, D x ≤ M - m :=
    fun x hx => sub_le_sub_left (hm x hx) M
  have hDnn : ∀ x ∈ Metric.closedBall z ρ, 0 ≤ D x :=
    fun x hx => sub_nonneg.mpr (hM x hx)
  have hDz : D z = 0 := by simp [hDdef, hMz]
  -- the reverse mean-value inequality for the deficit
  have hDavg : ∀ p ∈ Metric.ball z ρ, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball z ρ →
      Real.circleAverage D p r ≤ D p := by
    intro p hp r hr hsub
    have hsub' : Metric.closedBall p r ⊆ Metric.closedBall z ρ :=
      fun x hx => Metric.ball_subset_closedBall (hsub hx)
    have hsub'' : Metric.closedBall p |r| ⊆ Metric.closedBall z ρ := by
      intro x hx
      rw [abs_of_pos hr] at hx
      exact hsub' hx
    have hmeas : Measurable fun θ : ℝ => f (circleMap p r θ) :=
      measurable_circleMap_comp_of_upperSemicontinuousOn (husc.mono hsub'')
    have hbdd : ∀ x ∈ Metric.sphere p |r|, ‖f x‖ ≤ max |M| |m| := by
      intro x hx
      have hxρ : x ∈ Metric.closedBall z ρ :=
        hsub'' (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hx)))
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hm x hxρ, neg_abs_le m, le_max_right |M| |m|],
             by linarith [hM x hxρ, le_abs_self M, le_max_left |M| |m|]⟩
    have hint : CircleIntegrable f p r := circleIntegrable_of_bound hmeas hbdd
    have hintC : CircleIntegrable (fun _ : ℂ => M) p r := circleIntegrable_const M p r
    have hlin : Real.circleAverage D p r = M - Real.circleAverage f p r := by
      rw [hDdef, Real.circleAverage_fun_sub hintC hint, Real.circleAverage_const]
    rw [hlin]
    linarith [hmvi p hp r hr hsub]
  -- every point of `{D = 0}` in the ball has a neighbourhood of such points
  have hkey : ∀ x ∈ Metric.ball z ρ, D x = 0 → ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ Metric.ball z ρ ∧
      ∀ y ∈ Metric.ball x ε, D y = 0 := by
    intro x hxball hxD
    refine ⟨(ρ - dist x z) / 2, by have h := Metric.mem_ball.mp hxball; linarith, ?_, ?_⟩
    · intro y hy
      have hyd : dist y x < (ρ - dist x z) / 2 := Metric.mem_ball.mp hy
      rw [Metric.mem_ball]
      calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
        _ < (ρ - dist x z) / 2 + dist x z := by linarith
        _ < ρ := by have h := Metric.mem_ball.mp hxball; linarith
    · intro y hy
      rcases eq_or_ne y x with rfl | hyne
      · exact hxD
      · set r : ℝ := dist y x with hrdef
        have hr : 0 < r := dist_pos.mpr hyne
        have hsub : Metric.closedBall x r ⊆ Metric.ball z ρ := by
          intro u hu
          have hud : dist u x ≤ r := Metric.mem_closedBall.mp hu
          rw [Metric.mem_ball]
          have hyd : dist y x < (ρ - dist x z) / 2 := Metric.mem_ball.mp hy
          have hxz : dist x z < ρ := Metric.mem_ball.mp hxball
          calc dist u z ≤ dist u x + dist x z := dist_triangle _ _ _
            _ ≤ r + dist x z := by linarith
            _ < (ρ - dist x z) / 2 + dist x z := by linarith
            _ < ρ := by linarith
        have hsub' : Metric.closedBall x |r| ⊆ Metric.closedBall z ρ :=
          fun u hu => Metric.ball_subset_closedBall (hsub (by rwa [abs_of_pos hr] at hu))
        have hlsc' : LowerSemicontinuousOn D (Metric.closedBall x |r|) := hDlsc.mono hsub'
        have hnn : ∀ u ∈ Metric.sphere x |r|, 0 ≤ D u :=
          fun u hu => hDnn u (hsub' (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hu))))
        have hC' : ∀ u ∈ Metric.sphere x |r|, D u ≤ M - m :=
          fun u hu => hDbdd u (hsub' (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hu))))
        have havg0 : Real.circleAverage D x r = 0 := by
          have h1 : Real.circleAverage D x r ≤ 0 := by
            have := hDavg x hxball r hr hsub
            rwa [hxD] at this
          have h2 : 0 ≤ Real.circleAverage D x r :=
            Real.circleAverage_nonneg_of_nonneg
              (fun u hu => hDnn u (hsub' (Metric.mem_closedBall.mpr
                (le_of_eq (Metric.mem_sphere.mp hu)))))
          exact le_antisymm h1 h2
        have := eq_zero_on_sphere_of_circleAverage_eq_zero_of_lowerSemicontinuous
          (D := D) (c := x) (r := r) (C := M - m) hr hlsc' hnn hC' havg0
        have hycirc : y ∈ Metric.sphere x |r| := by
          rw [Metric.mem_sphere, ← hrdef, abs_of_pos hr]
        exact this y hycirc
  -- `{D = 0}` is clopen in the ball and nonempty, hence everything
  set S : Set ℂ := {x : ℂ | x ∈ Metric.ball z ρ ∧ D x = 0} with hSdef
  have hSopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨hxball, hxD⟩ := hx
    obtain ⟨ε, hε, hεsub, hεzero⟩ := hkey x hxball hxD
    exact ⟨ε, hε, fun y hy => ⟨hεsub hy, hεzero y hy⟩⟩
  have hScompl : IsOpen (Metric.ball z ρ \ S) := by
    have hset : Metric.ball z ρ \ S = Metric.ball z ρ ∩ {x | 0 < D x} := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, lt_of_le_of_ne (hDnn x (Metric.ball_subset_closedBall hx.1)) ?_⟩
        intro hc
        exact hx.2 ⟨hx.1, hc.symm⟩
      · intro hx
        exact ⟨hx.1, fun hc => absurd hc.2 (ne_of_gt hx.2)⟩
    rw [hset]
    obtain ⟨u, huopen, hu⟩ := (lowerSemicontinuousOn_iff_preimage_Ioi.mp hDlsc) 0
    have hset2 : Metric.ball z ρ ∩ {x | 0 < D x} = Metric.ball z ρ ∩ u := by
      ext x
      constructor
      · intro hx
        have hmem : x ∈ Metric.closedBall z ρ ∩ D ⁻¹' Set.Ioi 0 :=
          ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩
        rw [hu] at hmem
        exact ⟨hx.1, hmem.2⟩
      · intro hx
        have hmem : x ∈ Metric.closedBall z ρ ∩ u :=
          ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩
        rw [← hu] at hmem
        exact ⟨hx.1, hmem.2⟩
    rw [hset2]
    exact isOpen_ball.inter huopen
  have hcover : Metric.ball z ρ ⊆ S ∪ (Metric.ball z ρ \ S) := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hdisj : Disjoint S (Metric.ball z ρ \ S) := by
    rw [Set.disjoint_left]
    intro x hxS hx
    exact hx.2 hxS
  have hne : (Metric.ball z ρ ∩ S).Nonempty :=
    ⟨z, Metric.mem_ball_self hρ, Metric.mem_ball_self hρ, hDz⟩
  have hsub : Metric.ball z ρ ⊆ S :=
    isPreconnected_ball.subset_left_of_subset_union hSopen hScompl hdisj hcover hne
  intro w hw
  have := (hsub hw).2
  have : D w = 0 := this
  simp only [hDdef] at this
  linarith


end Plane

/-- **Transport of upper semicontinuity through a chart.**  If `u` is upper semicontinuous at
every point of `U` and the closed chart ball of radius `|ρ|` around the base point pulls back into
`U`, then the pullback `u ∘ (chartAt ℂ x₀).symm` is upper semicontinuous on that closed ball. -/
theorem upperSemicontinuousOn_comp_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} {U : Set X} {x₀ : X} {ρ : ℝ}
    (husc : ∀ y ∈ U, UpperSemicontinuousAt u y)
    (hsub : ∀ z ∈ Metric.closedBall ((chartAt ℂ x₀) x₀) ρ,
        (chartAt ℂ x₀).symm z ∈ U)
    (htarget : ∀ z ∈ Metric.closedBall ((chartAt ℂ x₀) x₀) ρ, z ∈ (chartAt ℂ x₀).target) :
    UpperSemicontinuousOn (u ∘ (chartAt ℂ x₀).symm)
      (Metric.closedBall ((chartAt ℂ x₀) x₀) ρ) := by
  intro z hz t ht
  have hcont : ContinuousAt (chartAt ℂ x₀).symm z :=
    (chartAt ℂ x₀).continuousAt_symm (htarget z hz)
  have h1 : ∀ᶠ y in 𝓝 ((chartAt ℂ x₀).symm z), u y < t :=
    husc _ (hsub z hz) t ht
  exact mem_nhdsWithin_of_mem_nhds (hcont.eventually h1)

section Manifold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Strong maximum principle at a point** (upper semicontinuous version, chart form).  If `u` is
upper semicontinuous on a neighbourhood `U` of `x`, satisfies the circle sub-mean-value inequality
at `x`, is bounded below on `U` and satisfies `u ≤ u x` on `U`, then `u = u x` on a neighbourhood
of `x`. -/
theorem usc_eqOn_of_le {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} {x : X} {U : Set X} (hU : U ∈ 𝓝 x)
    (husc : ∀ y ∈ U, UpperSemicontinuousAt u y)
    (hmvi : CircleSubMeanValueAtX u x)
    {m : ℝ} (hbl : ∀ y ∈ U, m ≤ u y)
    (hle : ∀ y ∈ U, u y ≤ u x) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V, u y = u x := by
  obtain ⟨ρ, hρ, htarget, hmvp⟩ := hmvi
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hVn : U ∩ (chartAt ℂ x).source ∈ 𝓝 x :=
    inter_mem hU ((chartAt ℂ x).open_source.mem_nhds hxsrc)
  have himg : (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source) ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).image_mem_nhds hxsrc hVn
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp himg
  set R : ℝ := min (ρ / 2) (ρ₁ / 2) with hRdef
  have hR : 0 < R := lt_min (by linarith) (by linarith)
  have hRρ : R ≤ ρ / 2 := min_le_left _ _
  have hRρ₁ : R ≤ ρ₁ / 2 := min_le_right _ _
  have hsub' : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) R, (chartAt ℂ x).symm z ∈ U := by
    intro z hz
    have hz1 : z ∈ Metric.ball ((chartAt ℂ x) x) ρ₁ := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.mp hz
      linarith
    obtain ⟨y, hy, hyz⟩ := hρ₁sub hz1
    have hysrc : y ∈ (chartAt ℂ x).source := hy.2
    have : (chartAt ℂ x).symm z = y := by rw [← hyz, (chartAt ℂ x).left_inv hysrc]
    rw [this]
    exact hy.1
  have htarget' : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) R, z ∈ (chartAt ℂ x).target := by
    intro z hz
    refine htarget ?_
    rw [Metric.mem_ball]
    have h1 := Metric.mem_closedBall.mp hz
    linarith
  have husc' : UpperSemicontinuousOn (u ∘ (chartAt ℂ x).symm)
      (Metric.closedBall ((chartAt ℂ x) x) R) :=
    upperSemicontinuousOn_comp_chart husc hsub' htarget'
  have hbound' : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) R,
      m ≤ (u ∘ (chartAt ℂ x).symm) z := fun z hz => hbl _ (hsub' z hz)
  have hmax' : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) R,
      (u ∘ (chartAt ℂ x).symm) z ≤ u x := by
    intro z hz
    have h1 : u ((chartAt ℂ x).symm z) ≤ u x := hle _ (hsub' z hz)
    simpa only [Function.comp_apply] using h1
  have hMz : (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = u x := by
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hxsrc]
  have hmvp' : ∀ p ∈ Metric.ball ((chartAt ℂ x) x) R, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) R →
      (u ∘ (chartAt ℂ x).symm) p ≤ Real.circleAverage (u ∘ (chartAt ℂ x).symm) p r :=
    fun p hp r hr hpr =>
      hmvp p (Metric.ball_subset_ball (by linarith) hp) r hr
        (hpr.trans (Metric.ball_subset_ball (by linarith)))
  have heq := eqOn_ball_of_isMaxOn_of_upperSemicontinuous (f := u ∘ (chartAt ℂ x).symm)
    (z := (chartAt ℂ x) x) (ρ := R) (M := u x) (m := m) hR husc' hbound' hmax' hMz hmvp'
  have hmem : (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) R ∈ 𝓝 x := by
    have h1 : Metric.ball ((chartAt ℂ x) x) R ∈ 𝓝 ((chartAt ℂ x) x) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)
    have h2 : (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) R ∈ 𝓝 x :=
      ((chartAt ℂ x).continuousAt hxsrc).eventually h1
    have h3 : (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) R ∩ (chartAt ℂ x).source ∈ 𝓝 x :=
      inter_mem h2 ((chartAt ℂ x).open_source.mem_nhds hxsrc)
    refine Filter.mem_of_superset h3 ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨(chartAt ℂ x) y, hy1, (chartAt ℂ x).left_inv hy2⟩
  refine ⟨(chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) R, hmem, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact heq z hz

/-- Upper semicontinuity within a neighbourhood gives upper semicontinuity at that point. -/
theorem UpperSemicontinuousWithinAt.upperSemicontinuousAt_of_mem {u : X → ℝ} {U : Set X} {x : X}
    (h : UpperSemicontinuousWithinAt u U x) (hU : U ∈ 𝓝 x) : UpperSemicontinuousAt u x := by
  intro t ht
  obtain ⟨T, hT, hTS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (h t ht)
  exact Filter.mem_of_superset (inter_mem hT hU) hTS

/-- **Maximum principle for upper semicontinuous functions with the circle sub-mean-value
inequality**, on a preconnected relatively compact open set. -/
theorem usc_le_of_circleSubMeanValue_preconnected {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    {U : Set X} (hU : IsOpen U) (hUpc : IsPreconnected U) {v : X → ℝ}
    (husc : UpperSemicontinuousOn v U)
    (hmvi : ∀ x ∈ U, CircleSubMeanValueAtX v x)
    (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty) {a m : ℝ}
    (hbl : ∀ x ∈ U, m ≤ v x)
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, v z ≤ a + ε) :
    ∀ z ∈ U, v z ≤ a := by
  rintro z₀ hz₀
  by_contra hcon
  simp only [not_le] at hcon
  have hza : a < v z₀ := hcon
  set δ : ℝ := (v z₀ - a) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδle : a + δ ≤ v z₀ := by rw [hδdef]; linarith
  set A : Set X := {z : X | z ∈ U ∧ a + δ ≤ v z} with hAdef
  have hz₀A : z₀ ∈ A := ⟨hz₀, hδle⟩
  have hAne : A.Nonempty := ⟨z₀, hz₀A⟩
  have hAU : A ⊆ U := fun z hz => hz.1
  have hAsub : A ⊆ closure U := fun z hz => subset_closure hz.1
  -- `A` is closed
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    by_cases hxU : x ∈ U
    · haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have h1 : ∀ ε : ℝ, 0 < ε → a + δ - ε ≤ v x := by
        intro ε hε
        have h2 : ∀ᶠ z in 𝓝[A] x, v z < v x + ε :=
          Filter.le_def.mp (nhdsWithin_mono x hAU) _ (husc x hxU (v x + ε) (by linarith))
        obtain ⟨z, hzv, hzA⟩ := (h2.and self_mem_nhdsWithin).exists
        linarith [hzA.2]
      refine ⟨hxU, ?_⟩
      by_contra hcon
      push Not at hcon
      exact absurd (h1 ((a + δ - v x) / 2) (by linarith)) (by linarith)
    · exfalso
      have hxfront : x ∈ frontier U := by
        refine ⟨closure_mono hAU hx, fun hxint => hxU (interior_subset hxint)⟩
      haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hlim' := hlim x hxfront (δ / 2) (by linarith)
      have hlim'' : ∀ᶠ z in 𝓝[A] x, v z ≤ a + δ / 2 :=
        Filter.le_def.mp (nhdsWithin_mono x hAU) _ hlim'
      obtain ⟨z, hzv, hzA⟩ := (hlim''.and self_mem_nhdsWithin).exists
      linarith [hzv, hzA.2]
  have hAcomp : IsCompact A := IsCompact.of_isClosed_subset hcomp hAclosed hAsub
  obtain ⟨p, hpA, hpMax⟩ := (husc.mono hAU).exists_isMaxOn hAne hAcomp
  set M : ℝ := v p with hMdef
  have hAle : a + δ ≤ M := by rw [hMdef]; exact hpA.2
  have hleM : ∀ z ∈ U, v z ≤ M := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hpMax hzA
    · have hlt : v z < a + δ := not_le.mp (fun h => hzA ⟨hz, h⟩)
      rw [hMdef]; linarith
  -- the level set is clopen in `U`
  set S : Set X := {z : X | z ∈ U ∧ v z = M} with hSdef
  have hpS : p ∈ S := ⟨hpA.1, by rw [hMdef]⟩
  have hSne : S.Nonempty := ⟨p, hpS⟩
  have hSU : S ⊆ U := fun z hz => hz.1
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hzS
    obtain ⟨V, hVn, hVeq⟩ := usc_eqOn_of_le (u := v) (x := z) (U := U)
      (hU.mem_nhds hzS.1)
      (fun y hy =>
        UpperSemicontinuousWithinAt.upperSemicontinuousAt_of_mem (husc y hy) (hU.mem_nhds hy))
      (hmvi z hzS.1) hbl
      (fun y hy => by rw [hzS.2]; exact hleM y hy)
    exact Filter.mem_of_superset (inter_mem hVn (hU.mem_nhds hzS.1))
      (fun y hy => ⟨hy.2, by rw [hVeq y hy.1, hzS.2]⟩)
  have hclU : closure U = U ∪ frontier U := by
    rw [closure_eq_interior_union_frontier, hU.interior_eq]
  by_cases hcl : closure S ∩ frontier U = ∅
  · have hcl_sub : closure S ⊆ U := by
      intro x hx
      have hxUcl : x ∈ closure U := closure_mono hSU hx
      rw [hclU] at hxUcl
      rcases hxUcl with h | h
      · exact h
      · have : x ∈ (∅ : Set X) := by rw [← hcl]; exact ⟨hx, h⟩
        exact this.elim
    have hSclosedX : IsClosed S := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hxU : x ∈ U := hcl_sub hx
      haveI : NeBot (𝓝[S] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hM : v x = M := by
        refine le_antisymm (hleM x hxU) ?_
        by_contra hlt
        push Not at hlt
        have hε : 0 < (M - v x) / 2 := by linarith
        have hT : ∀ᶠ z in 𝓝[S] x, v z < v x + (M - v x) / 2 :=
          Filter.le_def.mp (nhdsWithin_mono x hSU) _ (husc x hxU _ (by linarith))
        obtain ⟨z, hzv, hzS⟩ := (hT.and self_mem_nhdsWithin).exists
        have h1 : v z = M := hzS.2
        rw [h1] at hzv
        linarith
      exact ⟨hxU, hM⟩
    have hUsubS : U ⊆ S :=
      hUpc.subset_left_of_subset_union hSopen hSclosedX.isOpen_compl
        disjoint_compl_right
        (fun x hx => Or.elim (em (x ∈ S)) Or.inl (fun hxS => Or.inr hxS))
        ⟨p, hpS.1, hpS⟩
    have hSeq : S = U := Subset.antisymm hSU hUsubS
    exfalso
    have hfront : frontier U = ∅ := by
      have h1 : closure U = U := by
        rw [← hSeq]
        exact hSclosedX.closure_eq
      rw [frontier, h1, hU.interior_eq]
      exact Set.sdiff_self
    rw [hfront] at hne
    exact hne.ne_empty rfl
  · obtain ⟨ξ, hξ⟩ := Set.nonempty_iff_ne_empty.mpr hcl
    have hξcl : ξ ∈ closure S := hξ.1
    have hξfront : ξ ∈ frontier U := hξ.2
    have hlim' := hlim ξ hξfront ((M - a) / 2) (by linarith)
    haveI : NeBot (𝓝[S] ξ) := (mem_closure_iff_nhdsWithin_neBot).mp hξcl
    have hlim'' : ∀ᶠ z in 𝓝[S] ξ, v z ≤ a + (M - a) / 2 :=
      Filter.le_def.mp (nhdsWithin_mono ξ hSU) _ hlim'
    have henv : ∀ᶠ z in 𝓝[S] ξ, v z = M :=
      Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
    obtain ⟨z, hz1, hz2⟩ := (henv.and hlim'').exists
    linarith


end Manifold



section PlaneEnvelope

open scoped ENNReal




/-- The lower semicontinuous envelope `Q ↦ liminf_{Y → Q} g Y` of a globally bounded function is
lower semicontinuous. -/
theorem lsc_liminf_envelope {g : ℂ → ℝ} {C : ℝ} (h0 : ∀ Z, 0 ≤ g Z) (hC : ∀ Z, g Z ≤ C) :
    LowerSemicontinuous (fun Q : ℂ => Filter.liminf g (𝓝 Q)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  rw [isOpen_iff_mem_nhds]
  intro Q hQ
  simp only [Set.mem_preimage, Set.mem_Ioi] at hQ
  have hne : ({t : ℝ | ∀ᶠ Y in 𝓝 Q, t ≤ g Y}).Nonempty :=
    ⟨0, by filter_upwards with Y; exact h0 Y⟩
  have hbdd : BddAbove ({t : ℝ | ∀ᶠ Y in 𝓝 Q, t ≤ g Y}) := by
    refine ⟨C, fun t ht => ?_⟩
    obtain ⟨Y, hY1, hY2⟩ := (ht.and (Filter.Eventually.of_forall hC)).exists
    exact le_trans hY1 hY2
  rw [Filter.liminf_eq] at hQ
  obtain ⟨t, ht, hat⟩ := (lt_csSup_iff hbdd hne).mp hQ
  obtain ⟨U, hUsub, hUo, hQU⟩ := _root_.mem_nhds_iff.mp ht
  refine Filter.mem_of_superset (hUo.mem_nhds hQU) ?_
  intro Q' hQ'
  simp only [Set.mem_preimage, Set.mem_Ioi]
  have hmem : t ≤ Filter.liminf g (𝓝 Q') := by
    rw [Filter.liminf_eq]
    refine le_csSup ?_ ?_
    · refine ⟨C, fun s hs => ?_⟩
      obtain ⟨Y, hY1, hY2⟩ := (hs.and (Filter.Eventually.of_forall hC)).exists
      exact le_trans hY1 hY2
    · exact Filter.mem_of_superset (hUo.mem_nhds hQ') hUsub
  exact lt_of_lt_of_le hat hmem

/-- `ofReal` commutes with `liminf` (as an inequality) for a family bounded above. -/
theorem ENNReal.ofReal_liminf_le {ι : Type*} {x : ι → ℝ} {u : Filter ι} [NeBot u] {C : ℝ}
    (h0 : ∀ i, 0 ≤ x i) (hC : ∀ i, x i ≤ C) :
    ENNReal.ofReal (Filter.liminf x u) ≤ Filter.liminf (fun i => ENNReal.ofReal (x i)) u := by
  have hne : ({t : ℝ | ∀ᶠ i in u, t ≤ x i}).Nonempty :=
    ⟨0, by filter_upwards with i; exact h0 i⟩
  have hbdd : BddAbove ({t : ℝ | ∀ᶠ i in u, t ≤ x i}) := by
    refine ⟨C, fun t ht => ?_⟩
    obtain ⟨i, hi1, hi2⟩ := (ht.and (Filter.Eventually.of_forall hC)).exists
    exact le_trans hi1 hi2
  have hne2 : ({t : ℝ≥0∞ | ∀ᶠ i in u, t ≤ ENNReal.ofReal (x i)}).Nonempty :=
    ⟨0, by filter_upwards with i; exact bot_le⟩
  have hbdd2 : ∀ b ∈ {t : ℝ≥0∞ | ∀ᶠ i in u, t ≤ ENNReal.ofReal (x i)}, b ≤ ENNReal.ofReal C := by
    intro b hb
    obtain ⟨i, hi1, hi2⟩ :=
      (hb.and (Filter.Eventually.of_forall (fun i => ENNReal.ofReal_le_ofReal (hC i)))).exists
    exact le_trans hi1 hi2
  have htop : sSup {t : ℝ≥0∞ | ∀ᶠ i in u, t ≤ ENNReal.ofReal (x i)} ≠ ⊤ := by
    intro h
    have h1 : sSup {t : ℝ≥0∞ | ∀ᶠ i in u, t ≤ ENNReal.ofReal (x i)} ≤ ENNReal.ofReal C :=
      csSup_le hne2 hbdd2
    rw [h] at h1
    exact (ENNReal.ofReal_ne_top (r := C)) (top_le_iff.mp h1)
  rw [Filter.liminf_eq, Filter.liminf_eq, ENNReal.ofReal_le_iff_le_toReal htop]
  refine csSup_le hne ?_
  intro s hs
  have hsS : ENNReal.ofReal s ∈ {t : ℝ≥0∞ | ∀ᶠ i in u, t ≤ ENNReal.ofReal (x i)} := by
    filter_upwards [hs] with i hi
    exact ENNReal.ofReal_le_ofReal hi
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mp
    (le_csSup ⟨ENNReal.ofReal C, hbdd2⟩ hsS)



theorem circleAverage_liminf_le_of_circleAverage_le {g : ℂ → ℝ} {P : ℂ} {r C R : ℝ}
    (hr : 0 < r) (hR : r < R)
    (hmeas : ∀ Q ∈ Metric.ball P R, AEStronglyMeasurable (fun θ : ℝ => g (circleMap Q r θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))))
    (h0 : ∀ Z, 0 ≤ g Z) (hC : ∀ Z, g Z ≤ C)
    (hmvi : ∀ Q ∈ Metric.ball P R, Metric.closedBall Q r ⊆ Metric.ball P R →
        Real.circleAverage g Q r ≤ g Q) :
    Real.circleAverage (fun Q => Filter.liminf g (𝓝 Q)) P r ≤ Filter.liminf g (𝓝 P) := by
  classical
  have hL0 : ∀ Q : ℂ, 0 ≤ Filter.liminf g (𝓝 Q) := by
    intro Q
    rw [Filter.liminf_eq]
    refine le_csSup ?_ ?_
    · refine ⟨C, fun t ht => ?_⟩
      obtain ⟨Y, hY1, hY2⟩ := (ht.and (Filter.Eventually.of_forall hC)).exists
      exact le_trans hY1 hY2
    · filter_upwards with Y; exact h0 Y
  have hLC : ∀ Q : ℂ, Filter.liminf g (𝓝 Q) ≤ C := by
    intro Q
    rw [Filter.liminf_eq]
    refine csSup_le ?_ ?_
    · exact ⟨0, by filter_upwards with Y; exact h0 Y⟩
    · intro t ht
      obtain ⟨Y, hY1, hY2⟩ := (ht.and (Filter.Eventually.of_forall hC)).exists
      exact le_trans hY1 hY2
  have hLlsc : LowerSemicontinuous (fun Q : ℂ => Filter.liminf g (𝓝 Q)) := lsc_liminf_envelope h0 hC
  have hLmeas : Measurable (fun Q : ℂ => Filter.liminf g (𝓝 Q)) := hLlsc.measurable
  -- the initial integral is a genuine integral
  have hLi : Integrable (fun θ : ℝ => Filter.liminf g (𝓝 (circleMap P r θ)))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    refine Integrable.of_bound ?_ C ?_
    · exact (hLmeas.comp (continuous_circleMap P r).measurable).aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0 _)]
      exact hLC _
  -- Step 1
  have step1 : ENNReal.ofReal (∫ θ in (0:ℝ)..2 * Real.pi, Filter.liminf g (𝓝 (circleMap P r θ)))
      = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          ENNReal.ofReal (Filter.liminf g (𝓝 (circleMap P r θ))) := by
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLi
      (Filter.Eventually.of_forall (fun θ => hL0 _))
  -- Step 2 (pointwise)
  have hpt : ∀ θ : ℝ, ENNReal.ofReal (Filter.liminf g (𝓝 (circleMap P r θ)))
      ≤ Filter.liminf (fun Q : ℂ => ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) := by
    intro θ
    have hcont : Continuous (fun Q : ℂ => circleMap Q r θ) := by
      simp only [circleMap]
      fun_prop
    have h1 : Filter.liminf g (𝓝 (circleMap P r θ))
        ≤ Filter.liminf (fun Q : ℂ => g (circleMap Q r θ)) (𝓝 P) := by
      rw [Filter.liminf_eq, Filter.liminf_eq]
      refine csSup_le ?_ ?_
      · exact ⟨0, by filter_upwards with Y; exact h0 Y⟩
      · intro s hs
        have h2 : ∀ᶠ Q in 𝓝 P, s ≤ g (circleMap Q r θ) :=
          (hcont.continuousAt.tendsto.eventually hs)
        refine le_csSup ?_ h2
        refine ⟨C, fun t ht => ?_⟩
        obtain ⟨Y, hY1, hY2⟩ :=
          (ht.and (Filter.Eventually.of_forall (fun Y => hC (circleMap Y r θ)))).exists
        exact le_trans hY1 hY2
    calc ENNReal.ofReal (Filter.liminf g (𝓝 (circleMap P r θ)))
        ≤ ENNReal.ofReal (Filter.liminf (fun Q : ℂ => g (circleMap Q r θ)) (𝓝 P)) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ Filter.liminf (fun Q : ℂ => ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) :=
          ENNReal.ofReal_liminf_le (fun Q => h0 _) (fun Q => hC _)
  have step2 : (∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
        ENNReal.ofReal (Filter.liminf g (𝓝 (circleMap P r θ))))
      ≤ ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          Filter.liminf (fun Q : ℂ => ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) :=
    lintegral_mono (fun θ => hpt θ)
  -- Step 3 (Fatou)
  have step3 : (∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          Filter.liminf (fun Q : ℂ => ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P))
      ≤ Filter.liminf (fun Q : ℂ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) := by
    have hFmeas : ∀ Q : ℂ, AEMeasurable
        (fun θ : ℝ => if Q ∈ Metric.ball P R then ENNReal.ofReal (g (circleMap Q r θ)) else 0)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      intro Q
      by_cases hQ : Q ∈ Metric.ball P R
      · simp only [hQ, if_true]
        exact ENNReal.measurable_ofReal.comp_aemeasurable (hmeas Q hQ).aemeasurable
      · simp only [hQ, if_false]
        exact aemeasurable_const
    have hFatou := MeasureTheory.lintegral_liminf_le' (μ := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      (f := fun Q θ => if Q ∈ Metric.ball P R then ENNReal.ofReal (g (circleMap Q r θ)) else 0)
      (u := 𝓝 P) hFmeas
    have h1 : (∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          Filter.liminf (fun Q : ℂ => if Q ∈ Metric.ball P R then
            ENNReal.ofReal (g (circleMap Q r θ)) else 0) (𝓝 P))
        = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          Filter.liminf (fun Q : ℂ => ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) := by
      refine lintegral_congr (fun θ => ?_)
      refine Filter.liminf_congr ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))] with Q hQ
      simp only [hQ, if_true]
    have h2 : Filter.liminf (fun Q : ℂ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          (if Q ∈ Metric.ball P R then ENNReal.ofReal (g (circleMap Q r θ)) else 0)) (𝓝 P)
        = Filter.liminf (fun Q : ℂ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P) := by
      refine Filter.liminf_congr ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))] with Q hQ
      refine lintegral_congr (fun θ => ?_)
      simp only [hQ, if_true]
    rw [← h1, ← h2]
    exact hFatou
  -- Step 4 (rewrite the lintegral as ofReal of an integral)
  have hev : ∀ᶠ Q in 𝓝 P, Metric.closedBall Q r ⊆ Metric.ball P R := by
    have hb : Metric.ball P (R - r) ∈ 𝓝 P :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
    filter_upwards [hb] with Q hQ Z hZ
    rw [Metric.mem_ball] at hQ ⊢
    have hZr : dist Z Q ≤ r := by rwa [Metric.mem_closedBall] at hZ
    calc dist Z P ≤ dist Z Q + dist Q P := dist_triangle _ _ _
      _ ≤ r + dist Q P := by linarith
      _ < r + (R - r) := by linarith
      _ = R := by ring
  have step4 : Filter.liminf (fun Q : ℂ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          ENNReal.ofReal (g (circleMap Q r θ))) (𝓝 P)
      = Filter.liminf (fun Q : ℂ =>
          ENNReal.ofReal (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap Q r θ))) (𝓝 P) := by
    refine Filter.liminf_congr ?_
    filter_upwards [hev] with Q hQ
    have hint : Integrable (fun θ : ℝ => g (circleMap Q r θ))
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      refine Integrable.of_bound (hmeas Q (hQ (Metric.mem_closedBall_self hr.le))) C ?_
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact hC _
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun θ => h0 _))).symm
  -- Step 5
  have hIeq : ∀ Q : ℂ, (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap Q r θ))
      = 2 * Real.pi * Real.circleAverage g Q r := by
    intro Q
    rw [Real.circleAverage_def, smul_eq_mul, mul_inv_cancel_left₀ (by positivity : (2 * Real.pi) ≠ 0)]
  have hInn : ∀ Q : ℂ, 0 ≤ ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap Q r θ) := by
    intro Q
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    exact MeasureTheory.integral_nonneg (fun θ => h0 _)
  have step5 : Filter.liminf (fun Q : ℂ =>
        ENNReal.ofReal (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap Q r θ))) (𝓝 P)
      ≤ ENNReal.ofReal (2 * Real.pi * Filter.liminf g (𝓝 P)) := by
    rw [Filter.liminf_eq]
    refine csSup_le ?_ ?_
    · exact ⟨0, by filter_upwards with Q; exact bot_le⟩
    · intro b hb
      obtain ⟨Q0, hQ0⟩ := hb.exists
      have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ0
      have hbnd : ∀ᶠ Q in 𝓝 P, b.toReal / (2 * Real.pi) ≤ g Q := by
        filter_upwards [hb, hev] with Q hQ hQc
        have h1 : b.toReal ≤ ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap Q r θ) := by
          have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
          rwa [ENNReal.toReal_ofReal (hInn Q)] at h2
        have h3 : Real.circleAverage g Q r ≤ g Q :=
          hmvi Q (hQc (Metric.mem_closedBall_self hr.le)) hQc
        rw [hIeq Q] at h1
        have h5 : 2 * Real.pi * Real.circleAverage g Q r ≤ 2 * Real.pi * g Q :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [h1, h5]
      have h4 : b.toReal / (2 * Real.pi) ≤ Filter.liminf g (𝓝 P) := by
        rw [Filter.liminf_eq]
        refine le_csSup ?_ hbnd
        refine ⟨C, fun t ht => ?_⟩
        obtain ⟨Y, hY1, hY2⟩ := (ht.and (Filter.Eventually.of_forall hC)).exists
        exact le_trans hY1 hY2
      calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbtop).symm
        _ ≤ ENNReal.ofReal (2 * Real.pi * Filter.liminf g (𝓝 P)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)] at h4
            nlinarith [h4]
  -- Assembly
  have hbridge : ENNReal.ofReal (∫ θ in (0:ℝ)..2 * Real.pi,
        Filter.liminf g (𝓝 (circleMap P r θ)))
      ≤ ENNReal.ofReal (2 * Real.pi * Filter.liminf g (𝓝 P)) := by
    rw [step1]
    exact step2.trans (step3.trans (by rw [step4]; exact step5))
  have hfinal : (∫ θ in (0:ℝ)..2 * Real.pi, Filter.liminf g (𝓝 (circleMap P r θ)))
      ≤ 2 * Real.pi * Filter.liminf g (𝓝 P) :=
    (ENNReal.ofReal_le_ofReal_iff (by have := hL0 P; positivity)).mp hbridge
  rw [Real.circleAverage_def, smul_eq_mul]
  calc (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, Filter.liminf g (𝓝 (circleMap P r θ)))
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * Filter.liminf g (𝓝 P)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = Filter.liminf g (𝓝 P) := by
        rw [inv_mul_cancel_left₀ (by positivity : (2 * Real.pi) ≠ 0)]



section EnvelopeTransfer

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The upper semicontinuous envelope `Q ↦ limsup_{Y → Q} g Y` of a globally bounded function is
upper semicontinuous. -/
theorem usc_limsup_envelope {g : ℂ → ℝ} {m K : ℝ} (hm : ∀ Z, m ≤ g Z) (hK : ∀ Z, g Z ≤ K) :
    UpperSemicontinuous (fun Q : ℂ => Filter.limsup g (𝓝 Q)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro a
  rw [isOpen_iff_mem_nhds]
  intro Q hQ
  simp only [Set.mem_preimage, Set.mem_Iio] at hQ
  have hne : ({t : ℝ | ∀ᶠ Y in 𝓝 Q, g Y ≤ t}).Nonempty :=
    ⟨K, by filter_upwards with Y; exact hK Y⟩
  have hbdd : BddBelow ({t : ℝ | ∀ᶠ Y in 𝓝 Q, g Y ≤ t}) := by
    refine ⟨m, fun t ht => ?_⟩
    obtain ⟨Y, hY1, hY2⟩ := (ht.and (Filter.Eventually.of_forall hm)).exists
    exact le_trans hY2 hY1
  rw [Filter.limsup_eq] at hQ
  obtain ⟨t, ht, hta⟩ := (csInf_lt_iff hbdd hne).mp hQ
  obtain ⟨U, hUsub, hUo, hQU⟩ := _root_.mem_nhds_iff.mp ht
  refine Filter.mem_of_superset (hUo.mem_nhds hQU) ?_
  intro Q' hQ'
  simp only [Set.mem_preimage, Set.mem_Iio]
  have : Filter.limsup g (𝓝 Q') ≤ t := by
    rw [Filter.limsup_eq]
    refine csInf_le ?_ ?_
    · refine ⟨m, fun s hs => ?_⟩
      obtain ⟨Y, hY1, hY2⟩ := (hs.and (Filter.Eventually.of_forall hm)).exists
      exact le_trans hY2 hY1
    · exact Filter.mem_of_superset (hUo.mem_nhds hQ') hUsub
  linarith

/-- The envelope of `w` along the trace filter of `U`, transported to the chart at `x`, is the
limsup envelope of the pullback `w ∘ (chartAt ℂ x).symm`. -/
theorem uscEnv_comp_chart_eq_limsup {U : Set X} (hUo : IsOpen U) {w : X → ℝ} {x : X} {ρ : ℝ}
    (hρ : 0 < ρ)
    (htarget : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hU : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source)) :
    ∀ Z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
      Work.SimplyConnected.ABS.uscEnv U w ((chartAt ℂ x).symm Z) =
        Filter.limsup (fun Y => w ((chartAt ℂ x).symm Y)) (𝓝 Z) := by
  intro Z hZ
  obtain ⟨y, hy, hyZ⟩ := hU hZ
  have hZt : Z ∈ (chartAt ℂ x).target := htarget hZ
  have hsymm : (chartAt ℂ x).symm Z = y := by
    rw [← hyZ, (chartAt ℂ x).left_inv hy.2]
  have h2 : Filter.map (chartAt ℂ x).symm (𝓝 Z) = 𝓝 y := by
    rw [← hsymm]
    exact (chartAt ℂ x).symm.map_nhds_eq hZt
  have h1 : Work.SimplyConnected.ABS.uscEnv U w ((chartAt ℂ x).symm Z)
      = Filter.limsup w (𝓝[U] ((chartAt ℂ x).symm Z)) :=
    Work.SimplyConnected.ABS.uscEnv_eq_limsup U w _
  rw [h1, hsymm, nhdsWithin_eq_nhds.mpr (hUo.mem_nhds hy.1)]
  rw [← h2]
  exact (Filter.limsup_comp w ((chartAt ℂ x).symm) (𝓝 Z)).symm

/-- For a circle lying inside a chart ball, the function `θ ↦ K - w (c.symm (circleMap Q r θ))` is
upper semicontinuous (as a function of `θ`). -/
theorem upperSemicontinuous_comp_chart_circle {U : Set X} {w : X → ℝ} {x : X} {K R₀ : ℝ}
    {Q : ℂ} {r : ℝ}
    (hlsc : ∀ y ∈ U, LowerSemicontinuousAt w y)
    (htarget : Metric.ball ((chartAt ℂ x) x) R₀ ⊆ (chartAt ℂ x).target)
    (hU : Metric.ball ((chartAt ℂ x) x) R₀ ⊆ (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source))
    (hsub : ∀ θ : ℝ, circleMap Q r θ ∈ Metric.ball ((chartAt ℂ x) x) R₀) :
    UpperSemicontinuous (fun θ : ℝ => K - w ((chartAt ℂ x).symm (circleMap Q r θ))) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro a
  rw [isOpen_iff_mem_nhds]
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_Iio] at hθ
  have hmemt : circleMap Q r θ ∈ (chartAt ℂ x).target := htarget (hsub θ)
  have hsym : (chartAt ℂ x).symm (circleMap Q r θ) ∈ U := by
    obtain ⟨y, hy, hyZ⟩ := hU (hsub θ)
    rw [← hyZ, (chartAt ℂ x).left_inv hy.2]
    exact hy.1
  have hcont : Tendsto (fun θ' : ℝ => (chartAt ℂ x).symm (circleMap Q r θ')) (𝓝 θ)
      (𝓝 ((chartAt ℂ x).symm (circleMap Q r θ))) :=
    ((chartAt ℂ x).continuousAt_symm hmemt).tendsto.comp (continuous_circleMap Q r).continuousAt
  have h2 : ∀ᶠ y in 𝓝 ((chartAt ℂ x).symm (circleMap Q r θ)), K - w y < a := by
    have h3 := hlsc _ hsym (K - a) (by linarith)
    filter_upwards [h3] with y hy
    linarith
  refine Filter.mem_of_superset (hcont.eventually h2) ?_
  intro θ' hθ'
  exact hθ'




/-- **The circle sub-mean-value inequality transfers to the upper semicontinuous envelope.** -/
theorem circleSubMeanValueAtX_uscEnv {U : Set X} (hUo : IsOpen U) {w : X → ℝ} {K : ℝ}
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x) (hbdd : ∀ x ∈ U, w x ≤ K)
    {x : X} (hx : x ∈ U) (hmvi : CircleSubMeanValueAtX w x) :
    CircleSubMeanValueAtX (uscEnv U w) x := by
  classical
  obtain ⟨ρ₀, hρ₀, htarget₀, hmv₀⟩ := hmvi
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨ρ₁, hρ₁, hball₁⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆
      (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source) :=
    Metric.mem_nhds_iff.mp ((chartAt ℂ x).image_mem_nhds hxsrc
      (inter_mem (hUo.mem_nhds hx) ((chartAt ℂ x).open_source.mem_nhds hxsrc)))
  set P₀ : ℂ := (chartAt ℂ x) x with hP₀
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  set R : ℝ := min ρ₀ ρ₁ / 32 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have h3 : 3 * R < min ρ₀ ρ₁ := by rw [hRdef]; linarith
  have h5 : 5 * R < min ρ₀ ρ₁ := by rw [hRdef]; linarith
  have h8 : 8 * R < min ρ₀ ρ₁ := by rw [hRdef]; linarith
  have h8le : 8 * R ≤ ρ₁ := le_trans (le_of_lt h8) (min_le_right _ _)
  have h16 : 16 * R < min ρ₀ ρ₁ := by rw [hRdef]; linarith
  have hballT : Metric.ball P₀ (8 * R) ⊆ (chartAt ℂ x).target := by
    intro Z hZ
    refine htarget₀ ?_
    rw [Metric.mem_ball] at hZ ⊢
    exact lt_of_lt_of_le (lt_trans hZ h8) (min_le_left _ _)
  have hballU8 : Metric.ball P₀ (8 * R) ⊆ (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source) :=
    fun Z hZ => hball₁ (Metric.ball_subset_ball h8le hZ)
  have hmem16 : ∀ Z ∈ Metric.closedBall P₀ (16 * R),
      Z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm Z ∈ U := by
    intro Z hZ
    have hd : dist Z P₀ ≤ 16 * R := Metric.mem_closedBall.mp hZ
    have hρ : dist Z P₀ < min ρ₀ ρ₁ := lt_of_le_of_lt hd h16
    have h1 : Z ∈ (chartAt ℂ x).target :=
      htarget₀ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hρ (min_le_left _ _))
    obtain ⟨y, hy, hyZ⟩ :=
      hball₁ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hρ (min_le_right _ _))
    refine ⟨h1, ?_⟩
    rw [← hyZ, (chartAt ℂ x).left_inv hy.2]
    exact hy.1
  have hKccomp : IsCompact ((chartAt ℂ x).symm '' Metric.closedBall P₀ (16 * R)) :=
    (isCompact_closedBall P₀ (16 * R)).image_of_continuousOn
      ((chartAt ℂ x).continuousOn_symm.mono (fun Z hZ => (hmem16 Z hZ).1))
  have hlscOn : LowerSemicontinuousOn w ((chartAt ℂ x).symm '' Metric.closedBall P₀ (16 * R)) := by
    rintro y ⟨Z, hZ, rfl⟩
    exact (hlsc _ ((hmem16 Z hZ).2)).lowerSemicontinuousWithinAt _
  obtain ⟨m, hm⟩ := hlscOn.bddBelow_of_isCompact hKccomp
  have hmKc : ∀ Z ∈ Metric.closedBall P₀ (16 * R), m ≤ w ((chartAt ℂ x).symm Z) :=
    fun Z hZ => hm (Set.mem_image_of_mem w (Set.mem_image_of_mem (chartAt ℂ x).symm hZ))
  have hmle : m ≤ K := by
    have hP₀mem : P₀ ∈ Metric.closedBall P₀ (16 * R) :=
      Metric.mem_closedBall_self (by linarith [hRpos])
    have h1 : m ≤ w ((chartAt ℂ x).symm P₀) := hmKc P₀ hP₀mem
    have h2 : w ((chartAt ℂ x).symm P₀) ≤ K := hbdd _ ((hmem16 P₀ hP₀mem).2)
    linarith
  set Wfn : ℂ → ℝ := fun Z =>
    if Z ∈ Metric.closedBall P₀ (8 * R) then w ((chartAt ℂ x).symm Z) else K with hWfn
  have hWfnD : ∀ Z ∈ Metric.closedBall P₀ (8 * R), Wfn Z = w ((chartAt ℂ x).symm Z) := by
    intro Z hZ; rw [hWfn]; simp only [hZ, if_true]
  have hDsub16 : Metric.closedBall P₀ (8 * R) ⊆ Metric.closedBall P₀ (16 * R) :=
    Metric.closedBall_subset_closedBall (by linarith [hRpos])
  have hWfn_ge : ∀ Z, m ≤ Wfn Z := by
    intro Z
    by_cases hZ : Z ∈ Metric.closedBall P₀ (8 * R)
    · rw [hWfnD Z hZ]
      exact hmKc Z (hDsub16 hZ)
    · rw [hWfn]; simp only [hZ, if_false]; exact hmle
  have hWfn_le : ∀ Z, Wfn Z ≤ K := by
    intro Z
    by_cases hZ : Z ∈ Metric.closedBall P₀ (8 * R)
    · rw [hWfnD Z hZ]
      exact hbdd _ ((hmem16 Z (hDsub16 hZ)).2)
    · rw [hWfn]; simp only [hZ, if_false]; exact le_refl K
  set g : ℂ → ℝ := fun Z => K - Wfn Z with hg
  have hg0 : ∀ Z, 0 ≤ g Z := by intro Z; rw [hg]; linarith [hWfn_le Z]
  have hgC : ∀ Z, g Z ≤ K - m := by intro Z; rw [hg]; linarith [hWfn_ge Z]
  set V : ℂ → ℝ := fun Z => Filter.limsup Wfn (𝓝 Z) with hV
  have hVusc : UpperSemicontinuous V := usc_limsup_envelope hWfn_ge hWfn_le
  have hVmeas : Measurable V := hVusc.measurable
  have hVm : ∀ Z, m ≤ V Z := by
    intro Z
    simp only [hV]
    rw [Filter.limsup_eq]
    refine le_csInf ?_ ?_
    · exact ⟨K, by filter_upwards with Y; exact hWfn_le Y⟩
    · intro t ht
      obtain ⟨Y, hY1, hY2⟩ := ((Filter.Eventually.of_forall hWfn_ge).and ht).exists
      linarith
  have hVK : ∀ Z, V Z ≤ K := by
    intro Z
    simp only [hV]
    rw [Filter.limsup_eq]
    refine csInf_le ?_ ?_
    · refine ⟨m, fun t ht => ?_⟩
      obtain ⟨Y, hY1, hY2⟩ := ((Filter.Eventually.of_forall hWfn_ge).and ht).exists
      linarith
    · exact Filter.Eventually.of_forall hWfn_le
  have hagree : ∀ Z ∈ Metric.ball P₀ (3 * R),
      Wfn =ᶠ[𝓝 Z] (fun Y => w ((chartAt ℂ x).symm Y)) := by
    intro Z hZ
    have hnb : Metric.ball Z (4 * R) ∈ 𝓝 Z :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith [hRpos]))
    filter_upwards [hnb] with Y hY
    refine hWfnD Y ?_
    rw [Metric.mem_closedBall]
    rw [Metric.mem_ball] at hY hZ
    exact le_of_lt (by
      calc dist Y P₀ ≤ dist Y Z + dist Z P₀ := dist_triangle _ _ _
        _ < 4 * R + 3 * R := by linarith
        _ = 7 * R := by ring
        _ ≤ 8 * R := by linarith [hRpos])
  have henv : ∀ Z ∈ Metric.ball P₀ (8 * R),
      uscEnv U w ((chartAt ℂ x).symm Z) =
        Filter.limsup (fun Y => w ((chartAt ℂ x).symm Y)) (𝓝 Z) :=
    uscEnv_comp_chart_eq_limsup hUo (by linarith) hballT hballU8
  have hVen : ∀ Z ∈ Metric.ball P₀ (3 * R), V Z = uscEnv U w ((chartAt ℂ x).symm Z) := by
    intro Z hZ
    simp only [hV]
    rw [Filter.limsup_congr (hagree Z hZ),
      henv Z (Metric.ball_subset_ball (by linarith [hRpos]) hZ)]
  refine ⟨R, hRpos, fun Z hZ => hballT (Metric.ball_subset_ball (by linarith [hRpos] : R ≤ 8 * R) hZ), ?_⟩
  intro P hP r hr hsub
  have hPdist : dist P P₀ < R := Metric.mem_ball.mp hP
  have hr2 : r < 2 * R := by
    have hPmem : P ∈ Metric.closedBall P r := Metric.mem_closedBall_self hr.le
    have hz : P + (r : ℂ) ∈ Metric.closedBall P r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp [Complex.norm_real, abs_of_pos hr]
    have hzR : dist P₀ (P + (r : ℂ)) < R := by
      have := hsub hz; rwa [Metric.mem_ball, dist_comm] at this
    have h5 : dist P (P + (r : ℂ)) = r := by
      rw [dist_eq_norm]; simp [Complex.norm_real, abs_of_pos hr]
    have h3 := dist_triangle P P₀ (P + (r : ℂ))
    linarith
  -- measurability hypothesis for the plane lemma
  have hmeasP : ∀ Q ∈ Metric.ball P (2 * R), AEStronglyMeasurable
      (fun θ : ℝ => g (circleMap Q r θ)) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    intro Q hQ
    have hQ3 : dist Q P₀ < 3 * R := by
      have h1 : dist Q P < 2 * R := Metric.mem_ball.mp hQ
      calc dist Q P₀ ≤ dist Q P + dist P P₀ := dist_triangle _ _ _
        _ < 2 * R + R := by linarith
        _ = 3 * R := by ring
    have hsub8 : ∀ θ : ℝ, circleMap Q r θ ∈ Metric.ball P₀ (8 * R) := by
      intro θ
      rw [Metric.mem_ball]
      have h1 : dist (circleMap Q r θ) Q ≤ r := by
        have h := Metric.mem_sphere.mp (circleMap_mem_sphere' Q r θ)
        rw [h, abs_of_pos hr]
      calc dist (circleMap Q r θ) P₀ ≤ dist (circleMap Q r θ) Q + dist Q P₀ :=
            dist_triangle _ _ _
        _ < r + 3 * R := by linarith
        _ < 5 * R := by linarith
        _ < 8 * R := by linarith
    have heq : (fun θ : ℝ => g (circleMap Q r θ))
        = fun θ : ℝ => K - w ((chartAt ℂ x).symm (circleMap Q r θ)) := by
      funext θ
      have hmemD : circleMap Q r θ ∈ Metric.closedBall P₀ (8 * R) :=
        le_of_lt (Metric.mem_ball.mp (hsub8 θ))
      rw [hg]
      change K - Wfn (circleMap Q r θ) = K - w ((chartAt ℂ x).symm (circleMap Q r θ))
      rw [hWfnD _ hmemD]
    rw [heq]
    exact ((upperSemicontinuous_comp_chart_circle (K := K) hlsc hballT hballU8
      hsub8).measurable).aestronglyMeasurable
  -- mean value inequality hypothesis for the plane lemma
  have hmviP : ∀ Q ∈ Metric.ball P (2 * R), Metric.closedBall Q r ⊆ Metric.ball P (2 * R) →
      Real.circleAverage g Q r ≤ g Q := by
    intro Q hQ hQr
    have hQP : dist Q P < 2 * R := Metric.mem_ball.mp hQ
    have hQ3 : dist Q P₀ < 3 * R := by
      calc dist Q P₀ ≤ dist Q P + dist P P₀ := dist_triangle _ _ _
        _ < 2 * R + R := by linarith
        _ = 3 * R := by ring
    have hQ5 : ∀ Z ∈ Metric.sphere Q |r|, dist Z P₀ < 5 * R := by
      intro Z hZ
      have h1 : dist Z Q ≤ r := by
        have h := Metric.mem_sphere.mp hZ
        rw [h, abs_of_pos hr]
      calc dist Z P₀ ≤ dist Z Q + dist Q P₀ := dist_triangle _ _ _
        _ < r + 3 * R := by linarith
        _ < 5 * R := by linarith
    have hQrρ₀ : Metric.closedBall Q r ⊆ Metric.ball P₀ ρ₀ := by
      refine Metric.closedBall_subset_ball' ?_
      have h1 : r + dist Q P₀ < 5 * R := by linarith [hr2, hQ3]
      exact lt_of_lt_of_le (lt_trans h1 h5) (min_le_left ρ₀ ρ₁)
    have hWint : CircleIntegrable Wfn Q r := by
      refine circleIntegrable_of_bound (C := max |m| |K|) ?_ ?_
      · have hsub8' : ∀ θ : ℝ, circleMap Q r θ ∈ Metric.ball P₀ (8 * R) := by
          intro θ
          rw [Metric.mem_ball]
          have h1 : dist (circleMap Q r θ) Q ≤ r := by
            have h := Metric.mem_sphere.mp (circleMap_mem_sphere' Q r θ)
            rw [h, abs_of_pos hr]
          calc dist (circleMap Q r θ) P₀ ≤ dist (circleMap Q r θ) Q + dist Q P₀ :=
                dist_triangle _ _ _
            _ < r + 3 * R := by linarith
            _ < 5 * R := by linarith
            _ < 8 * R := by linarith
        have heq : (fun θ : ℝ => Wfn (circleMap Q r θ))
            = fun θ : ℝ => w ((chartAt ℂ x).symm (circleMap Q r θ)) := by
          funext θ
          exact hWfnD _ (le_of_lt (Metric.mem_ball.mp (hsub8' θ)))
        rw [heq]
        have h2' := (upperSemicontinuous_comp_chart_circle (K := 0) hlsc hballT hballU8
          hsub8').measurable.neg
        change Measurable (fun θ : ℝ => -(0 - w ((chartAt ℂ x).symm (circleMap Q r θ)))) at h2'
        simpa only [neg_sub, sub_zero] using h2'
      · intro Z hZ
        have hmemD : Z ∈ Metric.closedBall P₀ (8 * R) :=
          Metric.mem_closedBall.mpr (le_of_lt (lt_trans (hQ5 Z hZ) (by linarith [hRpos])))
        rw [Real.norm_eq_abs]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have h3 : |m| ≤ max |m| |K| := le_max_left _ _
          have h4 : -|m| ≤ m := neg_abs_le m
          linarith [hWfn_ge Z]
        · have h3 : |K| ≤ max |m| |K| := le_max_right _ _
          have h4 : K ≤ |K| := le_abs_self K
          linarith [hWfn_le Z]
    have h1 : Real.circleAverage g Q r = K - Real.circleAverage Wfn Q r := by
      rw [hg, Real.circleAverage_fun_sub (circleIntegrable_const K Q r) hWint,
        Real.circleAverage_const]
    have h2 : Real.circleAverage Wfn Q r
        = Real.circleAverage (fun Z => w ((chartAt ℂ x).symm Z)) Q r :=
      Real.circleAverage_congr_sphere (fun Z hZ => hWfnD Z (Metric.mem_closedBall.mpr
        (le_of_lt (lt_trans (hQ5 Z hZ) (by linarith [hRpos])))))
    have h3 : (fun Z => w ((chartAt ℂ x).symm Z)) Q
        ≤ Real.circleAverage (fun Z => w ((chartAt ℂ x).symm Z)) Q r :=
      hmv₀ Q (by rw [Metric.mem_ball]; exact lt_of_lt_of_le (lt_trans hQ3 h3) (min_le_left _ _)) r hr hQrρ₀
    have h4 : Wfn Q = w ((chartAt ℂ x).symm Q) := hWfnD Q (le_of_lt (lt_trans hQ3 (by linarith [hRpos])))
    rw [h1, h2]
    change K - Real.circleAverage (fun Z => w ((chartAt ℂ x).symm Z)) Q r ≤ K - Wfn Q
    rw [h4]
    linarith
  have hplane := circleAverage_liminf_le_of_circleAverage_le (g := g) (P := P) (r := r)
    (C := K - m) (R := 2 * R) hr hr2 hmeasP hg0 hgC hmviP
  -- translate the plane lemma into the desired inequality
  have hLval : ∀ Z : ℂ, Filter.liminf g (𝓝 Z) = K - V Z := by
    intro Z
    have hbddW : IsBoundedUnder (fun a b : ℝ => a ≤ b) (𝓝 Z) Wfn := by
      refine ⟨K, ?_⟩
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall (fun Y => hWfn_le Y)
    have hcobddW : IsCoboundedUnder (fun a b : ℝ => a ≤ b) (𝓝 Z) Wfn := by
      refine ⟨m, ?_⟩
      intro a ha
      rw [Filter.eventually_map] at ha
      have h1 : ∀ᶠ Y in 𝓝 Z, m ≤ Wfn Y :=
        Filter.Eventually.of_forall (fun Y => hWfn_ge Y)
      obtain ⟨Y, hY1, hY2⟩ := (h1.and ha).exists
      linarith
    rw [hg]
    simp only [hV]
    exact liminf_const_sub (𝓝 Z) Wfn K hbddW hcobddW
  have hVint : CircleIntegrable V P r := by
    refine circleIntegrable_of_bound (C := max |m| |K|) ?_ ?_
    · exact hVmeas.comp (continuous_circleMap P r).measurable
    · intro Z hZ
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have ha : |m| ≤ max |m| |K| := le_max_left _ _
        have hb : -|m| ≤ m := neg_abs_le m
        linarith [hVm Z]
      · have ha : |K| ≤ max |m| |K| := le_max_right _ _
        have hb : K ≤ |K| := le_abs_self K
        linarith [hVK Z]
  have hLrel : Real.circleAverage (fun Z => Filter.liminf g (𝓝 Z)) P r
      = K - Real.circleAverage V P r := by
    have h1 : Real.circleAverage (fun Z => Filter.liminf g (𝓝 Z)) P r
        = Real.circleAverage (fun Z => K - V Z) P r :=
      Real.circleAverage_congr_sphere (fun Z _ => hLval Z)
    rw [h1, Real.circleAverage_fun_sub (circleIntegrable_const K P r) hVint,
      Real.circleAverage_const]
  have hEnvEq : ∀ Z ∈ Metric.sphere P |r|, uscEnv U w ((chartAt ℂ x).symm Z) = V Z := by
    intro Z hZ
    have h1 : dist Z P ≤ r := by
      have h := Metric.mem_sphere.mp hZ
      rw [h, abs_of_pos hr]
    have hZ3 : Z ∈ Metric.ball P₀ (3 * R) := by
      rw [Metric.mem_ball]
      calc dist Z P₀ ≤ dist Z P + dist P P₀ := dist_triangle _ _ _
        _ < r + R := by linarith
        _ < 3 * R := by linarith
    exact (hVen Z hZ3).symm
  have hVrel : Real.circleAverage V P r
      = Real.circleAverage (fun Z => uscEnv U w ((chartAt ℂ x).symm Z)) P r :=
    Real.circleAverage_congr_sphere (fun Z hZ => (hEnvEq Z hZ).symm)
  have hLP : Filter.liminf g (𝓝 P) = K - uscEnv U w ((chartAt ℂ x).symm P) := by
    rw [hLval P]
    have hP3 : P ∈ Metric.ball P₀ (3 * R) := by
      rw [Metric.mem_ball]; linarith
    rw [hVen P hP3]
  rw [hLrel, hVrel, hLP] at hplane
  change uscEnv U w ((chartAt ℂ x).symm P)
    ≤ Real.circleAverage (fun Z => uscEnv U w ((chartAt ℂ x).symm Z)) P r
  linarith



end EnvelopeTransfer

section Assembly


variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]



/-- The envelope of an lsc function bounded above satisfies the frontier limsup bound. -/
theorem uscEnv_frontier_le {U : Set X} {w : X → ℝ} {K a : ℝ}
    (hUo : IsOpen U) (hbdd : ∀ x ∈ U, w x ≤ K) (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x)
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, w z ≤ a + ε) :
    ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, uscEnv U w z ≤ a + ε := by
  intro ξ hξ ε hε
  have h1 : ∀ᶠ z in 𝓝[U] ξ, w z ≤ a + ε / 2 := hlim ξ hξ (ε / 2) (half_pos hε)
  rw [Filter.eventually_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter] at h1
  obtain ⟨T, hT, hTsub⟩ := h1
  obtain ⟨V, hVsub, hVopen, hξV⟩ := _root_.mem_nhds_iff.mp hT
  refine Filter.mem_of_superset
    (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hξV)) self_mem_nhdsWithin) ?_
  intro z hz
  have hzU : z ∈ U := hz.2
  have hne : (𝓝[U] z).NeBot :=
    (mem_closure_iff_nhdsWithin_neBot).mp (subset_closure hzU)
  have hlow : ∀ᶠ y in 𝓝[U] z, w z - 1 ≤ w y := by
    have h2 : ∀ᶠ y in 𝓝 z, w z - 1 < w y := hlsc z hzU (w z - 1) (by linarith)
    filter_upwards [mem_nhdsWithin_of_mem_nhds h2] with y hy
    simpa only [Set.mem_setOf_eq] using le_of_lt hy
  have hup : ∀ᶠ y in 𝓝[U] z, w y ≤ a + ε / 2 := by
    refine Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hz.1)) self_mem_nhdsWithin) ?_
    intro y hy
    exact hTsub ⟨hVsub hy.1, hy.2⟩
  have h3 : uscEnv U w z ≤ a + ε / 2 := uscEnv_le_of_eventually hne hlow hup
  exact le_trans h3 (by linarith [half_le_self hε.le (a := ε)])

/-- Component bookkeeping for the relatively compact open set. -/
theorem connectedComponentIn_basic {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hUo : IsOpen U) (hcomp : IsCompact (closure U))
    (hne : (frontier U).Nonempty) {z : X} (hz : z ∈ U) :
    IsOpen (connectedComponentIn U z) ∧ IsPreconnected (connectedComponentIn U z) ∧
      IsCompact (closure (connectedComponentIn U z)) ∧
      (frontier (connectedComponentIn U z)).Nonempty ∧
      frontier (connectedComponentIn U z) ⊆ frontier U := by
  refine ⟨hUo.connectedComponentIn, isPreconnected_connectedComponentIn, ?_, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hcomp isClosed_closure
      (closure_mono (connectedComponentIn_subset U z))
  · rw [nonempty_frontier_iff]
    refine ⟨⟨z, mem_connectedComponentIn hz⟩, fun huniv => ?_⟩
    have h1 : (U : Set X) = Set.univ := by
      rw [← Set.univ_subset_iff, ← huniv]
      exact connectedComponentIn_subset U z
    rw [h1, frontier_univ] at hne
    exact hne.ne_empty rfl
  · intro y hy
    refine ⟨closure_mono (connectedComponentIn_subset U z) hy.1, ?_⟩
    intro hyU
    obtain ⟨W, ⟨hWn, hWpc⟩, hWU⟩ :=
      (locallyConnectedSpace_iff_connected_basis.mp ‹LocallyConnectedSpace X› y).mem_iff.mp
        (hUo.mem_nhds (interior_subset hyU))
    obtain ⟨u, huW, huC⟩ := (mem_closure_iff_nhds.mp hy.1) W hWn
    have hpre : IsPreconnected (W ∪ connectedComponentIn U z) :=
      hWpc.union u huW huC isPreconnected_connectedComponentIn
    have hzC : z ∈ connectedComponentIn U z := mem_connectedComponentIn hz
    have hsub : W ∪ connectedComponentIn U z ⊆ connectedComponentIn U z :=
      IsPreconnected.subset_connectedComponentIn hpre (Set.mem_union_right _ hzC)
        (Set.union_subset hWU (connectedComponentIn_subset U z))
    have hyO : y ∈ interior W := by rwa [mem_interior_iff_mem_nhds]
    refine hy.2 ?_
    rw [hUo.connectedComponentIn.interior_eq]
    exact hsub (Set.mem_union_left _ (interior_subset hyO))

/-- A constant upper bound for the envelope of an lsc function. -/
theorem uscEnv_le_const {U : Set X} {w : X → ℝ} {K : ℝ} (hUo : IsOpen U)
    (hbdd : ∀ x ∈ U, w x ≤ K) (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x)
    {x : X} (hx : x ∈ U) : uscEnv U w x ≤ K := by
  refine uscEnv_le_of_eventually (m := w x - 1)
    ((mem_closure_iff_nhdsWithin_neBot).mp (subset_closure hx)) ?_ ?_
  · have h1 : ∀ᶠ y in 𝓝 x, w x - 1 < w y := hlsc x hx (w x - 1) (by linarith)
    filter_upwards [mem_nhdsWithin_of_mem_nhds h1] with y hy
    exact le_of_lt hy
  · exact mem_nhdsWithin_of_mem_nhds
      (Filter.mem_of_superset (hUo.mem_nhds hx) (fun y hy => hbdd y hy))

/-- The pullback of an upper semicontinuous function along a chart circle is measurable. -/
theorem measurable_comp_chart_circle_of_upperSemicontinuousOn {U : Set X} {f : X → ℝ} {x : X}
    {ρ : ℝ} (hf : UpperSemicontinuousOn f U)
    (htarget : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hU : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source))
    {p : ℂ} {r : ℝ} (hsub : ∀ θ : ℝ, circleMap p r θ ∈ Metric.ball ((chartAt ℂ x) x) ρ) :
    Measurable (fun θ : ℝ => f ((chartAt ℂ x).symm (circleMap p r θ))) := by
  refine measurable_of_Iio (fun a => ?_)
  have : IsOpen ((fun θ : ℝ => f ((chartAt ℂ x).symm (circleMap p r θ))) ⁻¹' Set.Iio a) := by
   rw [isOpen_iff_mem_nhds]
   intro θ hθ
   simp only [Set.mem_preimage, Set.mem_Iio] at hθ
   have hmemt : circleMap p r θ ∈ (chartAt ℂ x).target := htarget (hsub θ)
   have hsym : (chartAt ℂ x).symm (circleMap p r θ) ∈ U := by
     obtain ⟨y, hy, hyZ⟩ := hU (hsub θ)
     rw [← hyZ, (chartAt ℂ x).left_inv hy.2]
     exact hy.1
   have hcont : Tendsto (fun θ' : ℝ => (chartAt ℂ x).symm (circleMap p r θ')) (𝓝 θ)
       (𝓝 ((chartAt ℂ x).symm (circleMap p r θ))) :=
     ((chartAt ℂ x).continuousAt_symm hmemt).tendsto.comp (continuous_circleMap p r).continuousAt
   have h2 : {y : X | f y < a} ∈ 𝓝[U] ((chartAt ℂ x).symm (circleMap p r θ)) :=
     hf _ hsym a hθ
   rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at h2
   obtain ⟨T, hT, hTsub⟩ := h2
   refine Filter.mem_of_superset (hcont.eventually hT) ?_
   intro θ' hθ'
   have hU' : (chartAt ℂ x).symm (circleMap p r θ') ∈ U := by
     obtain ⟨y, hy, hyZ⟩ := hU (hsub θ')
     rw [← hyZ, (chartAt ℂ x).left_inv hy.2]
     exact hy.1
   exact hTsub ⟨hθ', hU'⟩
  exact this.measurableSet

/-- A lower bound for `w` on the pull-back of a chart closed ball. -/
theorem bddBelow_chart_closedBall {U : Set X} {w : X → ℝ} {y : X} {ρ : ℝ} {p : ℂ} {r : ℝ}
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x)
    (htarget : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hU : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y) '' (U ∩ (chartAt ℂ y).source))
    (hsub : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ y) y) ρ) :
    ∃ m : ℝ, ∀ Z ∈ Metric.closedBall p r, m ≤ w ((chartAt ℂ y).symm Z) := by
  have hcontOn : ContinuousOn ((chartAt ℂ y).symm) (Metric.closedBall p r) :=
    ((chartAt ℂ y).continuousOn_symm).mono (fun Z hZ => htarget (hsub hZ))
  have hsubU : ∀ Z ∈ Metric.closedBall p r, (chartAt ℂ y).symm Z ∈ U := by
    intro Z hZ
    obtain ⟨u, hu, huZ⟩ := hU (hsub hZ)
    rw [← huZ, (chartAt ℂ y).left_inv hu.2]
    exact hu.1
  have hcomp : IsCompact ((chartAt ℂ y).symm '' Metric.closedBall p r) :=
    (isCompact_closedBall p r).image_of_continuousOn hcontOn
  have hlscOn : LowerSemicontinuousOn w ((chartAt ℂ y).symm '' Metric.closedBall p r) := by
    rintro _ ⟨Z, hZ, rfl⟩
    exact (hlsc _ (hsubU Z hZ)).lowerSemicontinuousWithinAt _
  obtain ⟨m, hm⟩ := hlscOn.bddBelow_of_isCompact hcomp
  exact ⟨m, fun Z hZ =>
    hm (Set.mem_image_of_mem w (Set.mem_image_of_mem (chartAt ℂ y).symm hZ))⟩


/-- Pointwise maximum with a constant preserves upper semicontinuity on a set. -/
theorem UpperSemicontinuousOn.max_const {u : X → ℝ} {C : Set X} {c : ℝ}
    (h : UpperSemicontinuousOn u C) : UpperSemicontinuousOn (fun y => max (u y) c) C := by
  intro x hx t ht
  have h1 : u x < t := lt_of_le_of_lt (le_max_left _ _) ht
  have h2 : c < t := lt_of_le_of_lt (le_max_right _ _) ht
  filter_upwards [h x hx t h1] with y hy
  exact max_lt hy h2

/-- **The main theorem.** -/
theorem lsc_le_of_circleSubMeanValue {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hUo : IsOpen U) {w : X → ℝ}
    (hlsc : ∀ x ∈ U, LowerSemicontinuousAt w x)
    (hmvi : ∀ x ∈ U, CircleSubMeanValueAtX w x)
    (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    {K a : ℝ} (hbdd : ∀ x ∈ U, w x ≤ K)
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in nhdsWithin ξ U, w z ≤ a + ε) :
    ∀ z ∈ U, w z ≤ a := by
  classical
  haveI hLC : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hleself : ∀ x ∈ U, w x ≤ uscEnv U w x := by
    intro x hx
    refine le_uscEnv ((mem_closure_iff_nhdsWithin_neBot).mp (subset_closure hx)) ?_ ?_
    · exact ⟨K, mem_nhdsWithin_of_mem_nhds
        (Filter.mem_of_superset (hUo.mem_nhds hx) (fun y hy => hbdd y hy))⟩
    · intro t ht
      exact (hlsc x hx t ht).filter_mono nhdsWithin_le_nhds
  intro z hz
  obtain ⟨hCo, hCpc, hCcomp, hCne, hCfront⟩ := connectedComponentIn_basic hUo hcomp hne hz
  have hCsub : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
  have hvusc : UpperSemicontinuousOn (fun y => max (uscEnv U w y) (a - 1))
      (connectedComponentIn U z) :=
    UpperSemicontinuousOn.max_const ((uscEnv_upperSemicontinuousOn hUo hbdd hlsc).mono hCsub)
  have hvmvi : ∀ y ∈ connectedComponentIn U z,
      CircleSubMeanValueAtX (fun x => max (uscEnv U w x) (a - 1)) y := by
    intro y hy
    obtain ⟨ρ₁, hρ₁, htgt₁, hmvi₁⟩ :=
      circleSubMeanValueAtX_uscEnv hUo hlsc hbdd (hCsub hy) (hmvi y (hCsub hy))
    have hyc : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
    obtain ⟨ρ₂, hρ₂, hU₂⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ y) y) ρ ⊆
        (chartAt ℂ y) '' (U ∩ (chartAt ℂ y).source) :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ y).image_mem_nhds hyc
        (inter_mem (hUo.mem_nhds (hCsub hy)) ((chartAt ℂ y).open_source.mem_nhds hyc)))
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_⟩
    · exact fun Z hZ => htgt₁ (Metric.ball_subset_ball (min_le_left _ _) hZ)
    · intro p hp r hr hsub
      have hp₁ : p ∈ Metric.ball ((chartAt ℂ y) y) ρ₁ := Metric.ball_subset_ball (min_le_left _ _) hp
      have hsub₁ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ y) y) ρ₁ :=
        hsub.trans (Metric.ball_subset_ball (min_le_left _ _))
      have hsubmin : ∀ θ : ℝ, circleMap p r θ ∈
          Metric.ball ((chartAt ℂ y) y) (min ρ₁ ρ₂) :=
        fun θ => hsub (Metric.sphere_subset_closedBall (by
          simpa only [abs_of_pos hr] using circleMap_mem_sphere' p r θ))
      -- the pullback of the envelope is measurable
      have hmeasV : Measurable
          (fun θ : ℝ => uscEnv U w ((chartAt ℂ y).symm (circleMap p r θ))) :=
        measurable_comp_chart_circle_of_upperSemicontinuousOn
          (uscEnv_upperSemicontinuousOn hUo hbdd hlsc)
          (fun Z hZ => htgt₁ (Metric.ball_subset_ball (min_le_left _ _) hZ))
          (fun Z hZ => hU₂ (Metric.ball_subset_ball (min_le_right _ _) hZ)) hsubmin
      -- a lower bound for `w` on the chart closed ball
      obtain ⟨m₀, hm₀⟩ := bddBelow_chart_closedBall hlsc
        (fun Z hZ => htgt₁ (Metric.ball_subset_ball (min_le_left _ _) hZ))
        (fun Z hZ => hU₂ (Metric.ball_subset_ball (min_le_right _ _) hZ)) hsub
      -- membership in `U` of the pulled-back points
      have hmemU : ∀ Z ∈ Metric.closedBall p r, (chartAt ℂ y).symm Z ∈ U := by
        intro Z hZ
        obtain ⟨u, hu, huZ⟩ := hU₂ (Metric.ball_subset_ball (min_le_right _ _) (hsub hZ))
        rw [← huZ, (chartAt ℂ y).left_inv hu.2]
        exact hu.1
      have hsphere : ∀ Z ∈ Metric.sphere p |r|, Z ∈ Metric.closedBall p r :=
        fun Z hZ => Metric.sphere_subset_closedBall (by simpa only [abs_of_pos hr] using hZ)
      have hIntV : CircleIntegrable (((uscEnv U w)) ∘ (chartAt ℂ y).symm) p r := by
        refine circleIntegrable_of_bound (C := max |m₀| |K|) hmeasV ?_
        intro Z hZ
        have hZU : (chartAt ℂ y).symm Z ∈ U := hmemU Z (hsphere Z hZ)
        have hlow : m₀ ≤ uscEnv U w ((chartAt ℂ y).symm Z) :=
          le_trans (hm₀ Z (hsphere Z hZ)) (hleself _ hZU)
        have hup : uscEnv U w ((chartAt ℂ y).symm Z) ≤ K := uscEnv_le_const hUo hbdd hlsc hZU
        rw [Real.norm_eq_abs]
        refine abs_le.mpr ⟨?_, ?_⟩
        · exact le_trans (neg_le_neg (le_max_left |m₀| |K|)) (le_trans (neg_abs_le m₀) hlow)
        · exact le_trans hup (le_trans (le_abs_self K) (le_max_right |m₀| |K|))
      have hIntG : CircleIntegrable
          (fun Z => max (uscEnv U w ((chartAt ℂ y).symm Z)) (a - 1)) p r := by
        refine circleIntegrable_of_bound (C := max (max |m₀| |K|) |a - 1|)
          (hmeasV.max measurable_const) ?_
        intro Z hZ
        have hZU : (chartAt ℂ y).symm Z ∈ U := hmemU Z (hsphere Z hZ)
        have hlow : m₀ ≤ uscEnv U w ((chartAt ℂ y).symm Z) :=
          le_trans (hm₀ Z (hsphere Z hZ)) (hleself _ hZU)
        have hup : uscEnv U w ((chartAt ℂ y).symm Z) ≤ K := uscEnv_le_const hUo hbdd hlsc hZU
        have hupper : uscEnv U w ((chartAt ℂ y).symm Z) ≤ max (max |m₀| |K|) |a - 1| :=
          le_trans hup (le_trans (le_trans (le_abs_self K) (le_max_right |m₀| |K|))
            (le_max_left (max |m₀| |K|) |a - 1|))
        have hlower : -(max (max |m₀| |K|) |a - 1|) ≤ m₀ :=
          le_trans (neg_le_neg (le_max_left (max |m₀| |K|) |a - 1|))
            (le_trans (neg_le_neg (le_max_left |m₀| |K|)) (neg_abs_le m₀))
        rw [Real.norm_eq_abs]
        refine abs_le.mpr ⟨?_, ?_⟩
        · exact le_trans (le_trans hlower hlow)
            (le_max_left (uscEnv U w ((chartAt ℂ y).symm Z)) (a - 1))
        · exact max_le hupper (le_trans (le_abs_self (a - 1)) (le_max_right (max |m₀| |K|) (|a - 1|)))
      -- monotonicity of the circle average
      have h1 : Real.circleAverage (((uscEnv U w)) ∘ (chartAt ℂ y).symm) p r
          ≤ Real.circleAverage
            (fun Z => max (((uscEnv U w)) ((chartAt ℂ y).symm Z)) (a - 1)) p r :=
        Real.circleAverage_mono hIntV hIntG (fun Z hZ => le_max_left _ _)
      have h2 : (a - 1 : ℝ) ≤ Real.circleAverage
            (fun Z => max (((uscEnv U w)) ((chartAt ℂ y).symm Z)) (a - 1)) p r := by
        have h := Real.circleAverage_mono (circleIntegrable_const (a - 1) p r) hIntG
          (fun Z hZ => le_max_right _ _)
        rwa [Real.circleAverage_const] at h
      have h3 : uscEnv U w ((chartAt ℂ y).symm p)
          ≤ Real.circleAverage (((uscEnv U w)) ∘ (chartAt ℂ y).symm) p r :=
        hmvi₁ p hp₁ r hr hsub₁
      change max (uscEnv U w ((chartAt ℂ y).symm p)) (a - 1)
        ≤ Real.circleAverage (fun Z => max (uscEnv U w ((chartAt ℂ y).symm Z)) (a - 1)) p r
      exact le_trans (max_le_max h3 le_rfl) (max_le h1 h2)
  -- the frontier bound
  have hvlim : ∀ ξ ∈ frontier (connectedComponentIn U z), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in 𝓝[connectedComponentIn U z] ξ, max (uscEnv U w x) (a - 1) ≤ a + ε := by
    intro ξ hξ ε hε
    have h1 : ∀ᶠ x in 𝓝[U] ξ, uscEnv U w x ≤ a + ε :=
      uscEnv_frontier_le hUo hbdd hlsc hlim ξ (hCfront hξ) ε hε
    have h2 : ∀ᶠ x in 𝓝[connectedComponentIn U z] ξ, uscEnv U w x ≤ a + ε :=
      nhdsWithin_mono ξ (fun x hx => hCsub hx) h1
    filter_upwards [h2] with x hx
    exact max_le hx (by linarith)
  -- apply the upper semicontinuous maximum principle
  have hmain := usc_le_of_circleSubMeanValue_preconnected (U := connectedComponentIn U z)
    hCo hCpc hvusc hvmvi hCcomp hCne (m := a - 1) (a := a)
    (fun x hx => le_max_right _ _) hvlim
  have hzC : z ∈ connectedComponentIn U z := mem_connectedComponentIn hz
  have hfin : max (uscEnv U w z) (a - 1) ≤ a := hmain z hzC
  have h1 : uscEnv U w z ≤ a := le_of_max_le_left hfin
  exact le_trans (hleself z hz) h1


end Assembly

end PlaneEnvelope

end Work.SimplyConnected.ABS
