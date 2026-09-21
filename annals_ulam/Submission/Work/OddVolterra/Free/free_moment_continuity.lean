import Mathlib
import Submission.Work.OddVolterra.Free.free_profile_continuity
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free
import Submission.Work.OddCurve.LowSlope.Extension

/-!
# Continuity of the two moment integrals in the cutting slope (free tips)

For a free-tip envelope curve the two moment integrals `(A)` and `(B)` of the odd case are
continuous functions of the cutting slope at every slope `s > 0`.

The proof has three steps.

* **A fixed interval.**  For slopes `u ≥ c` the section `(-(x u), y u)` is contained in
  `(-(x c), y c)`, and the integrand vanishes on the extra pieces
  (`Work.OddVolterra.Free.rad_nonpos_outside_free`), so the two moment integrals at slope `u`
  may be computed over the fixed interval `[-(x c), y c]`.
* **A clamped profile.**  On that fixed interval the (untruncated) profile is replaced by
  `g t = envProfileFree h x y (max (-(x c)) (min (y c) t))`, which agrees with it there and is
  *globally continuous* (`continuousOn_envProfileFree` plus continuity of the clamp), so that the
  parametric continuity rule applies.
* **A reparametrisation of the slope.**  The bump is replaced by `u ↦ h (c u)` with `c` a smooth
  bump reparametrisation which is the identity near `s`; this makes the integrand jointly
  continuous in `(u, t)` over `ℝ × ℝ` (in particular `deriv h` is only continuous on `(0,∞)`).
  Near `s` the two integrands agree.
-/

namespace Work.OddVolterra.Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## Transporting the moment integrals to a fixed interval -/

/-- **Passing to a fixed interval, with the vanishing only on the two bands that matter.**
If `f` vanishes on `[a,c]` and on `[d,b]`, then its integral over `[a,b]` is its integral over
`[c,d]`.  (This is `Work.OddCurve.intervalIntegral_eq_of_eq_zero_outside` with the vanishing
required only where the integral actually samples it.) -/
theorem intervalIntegral_eq_of_eq_zero_between {f : ℝ → ℝ} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hleft : ∀ t, a ≤ t → t ≤ c → f t = 0) (hright : ∀ t, d ≤ t → t ≤ b → f t = 0) :
    ∫ t in a..b, f t = ∫ t in c..d, f t := by
  have hab : a ≤ b := le_trans hac (le_trans hcd hdb)
  have hpoint : ∀ x, x ∈ Set.Ioc a b → f x = (Set.Ioc c d).indicator f x := by
    intro x hx
    by_cases hxc : x ≤ c
    · rw [hleft x hx.1.le hxc]
      exact (Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hxc)) f).symm
    · push Not at hxc
      by_cases hxd : x ≤ d
      · exact (Set.indicator_of_mem (s := Set.Ioc c d)
          (show x ∈ Set.Ioc c d from ⟨hxc, hxd⟩) f).symm
      · push Not at hxd
        rw [hright x hxd.le hx.2]
        exact (Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hxd)) f).symm
  have hsubset : Set.Ioc c d ⊆ Set.Ioc a b :=
    fun x hx => ⟨lt_of_le_of_lt hac hx.1, le_trans hx.2 hdb⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc (Eventually.of_forall hpoint)]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsubset]

/-- **`(A)` over the fixed interval `[-(x c), y c]`** for slopes `u ≥ c > 0`. -/
theorem momentA_eq_fixedInterval_free {n : ℕ} {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c u : ℝ} (hc : 0 < c) (hcu : c ≤ u) :
    Work.OddCurve.momentA n h x y (envProfileFree h x y) u =
      ∫ t in (-(x c))..(y c), Work.OddCurve.rad h (envProfileFree h x y) u t ^ n *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t) := by
  rcases eq_or_lt_of_le hcu with heq | hlt
  · subst heq
    rw [Work.OddCurve.momentA_def]
  · have hu : 0 < u := lt_trans hc hlt
    have hxu : x u < x c := H.strictAntiOn_x hc hu hlt
    have hyu : y u < y c := H.strictAntiOn_y hc hu hlt
    have hxu0 : 0 < x u := H.pos_x hu
    have hyu0 : 0 < y u := H.pos_y hu
    have hle1 : -(x c) ≤ -(x u) := by linarith
    have hle2 : -(x u) ≤ y u := by linarith
    have hle3 : y u ≤ y c := hyu.le
    have hrad := rad_nonpos_outside_free H hc hcu
    rw [Work.OddCurve.momentA_def]
    refine (intervalIntegral_eq_of_eq_zero_between (f := fun t => Work.OddCurve.rad h
      (envProfileFree h x y) u t ^ n * Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t))
      hle1 hle2 hle3 ?_ ?_).symm
    · intro t ht1 ht2
      simp [Real.sqrt_eq_zero_of_nonpos (hrad.2 t ht1 ht2)]
    · intro t ht1 ht2
      simp [Real.sqrt_eq_zero_of_nonpos (hrad.1 t ht1 ht2)]

/-- **`(B)` over the fixed interval `[-(x c), y c]`** for slopes `u ≥ c > 0`. -/
theorem momentB_eq_fixedInterval_free {n : ℕ} {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c u : ℝ} (hc : 0 < c) (hcu : c ≤ u) :
    Work.OddCurve.momentB n h x y (envProfileFree h x y) u =
      ∫ t in (-(x c))..(y c), Work.OddCurve.rad h (envProfileFree h x y) u t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t) * (t + deriv h u) := by
  rcases eq_or_lt_of_le hcu with heq | hlt
  · subst heq
    rw [Work.OddCurve.momentB_def]
  · have hu : 0 < u := lt_trans hc hlt
    have hxu : x u < x c := H.strictAntiOn_x hc hu hlt
    have hyu : y u < y c := H.strictAntiOn_y hc hu hlt
    have hxu0 : 0 < x u := H.pos_x hu
    have hyu0 : 0 < y u := H.pos_y hu
    have hle1 : -(x c) ≤ -(x u) := by linarith
    have hle2 : -(x u) ≤ y u := by linarith
    have hle3 : y u ≤ y c := hyu.le
    have hrad := rad_nonpos_outside_free H hc hcu
    rw [Work.OddCurve.momentB_def]
    refine (intervalIntegral_eq_of_eq_zero_between (f := fun t => Work.OddCurve.rad h
      (envProfileFree h x y) u t ^ (n - 1) *
      Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t) * (t + deriv h u))
      hle1 hle2 hle3 ?_ ?_).symm
    · intro t ht1 ht2
      simp [Real.sqrt_eq_zero_of_nonpos (hrad.2 t ht1 ht2)]
    · intro t ht1 ht2
      simp [Real.sqrt_eq_zero_of_nonpos (hrad.1 t ht1 ht2)]

/-! ## Continuity in the slope -/

/-- The clamped profile is continuous. -/
theorem continuous_clamp_envProfileFree {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ => envProfileFree h x y (max (-(x c)) (min (y c) t))) := by
  have hle : -(x c) ≤ y c := by
    have h1 := H.pos_x hc
    have h2 := H.pos_y hc
    linarith
  refine ContinuousOn.comp_continuous (continuousOn_envProfileFree H hc) ?_ ?_
  · fun_prop
  · intro t
    exact ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩

/-- The clamped profile agrees with the profile on the fixed interval. -/
theorem clamp_envProfileFree_eqOn {h x y : ℝ → ℝ} {c : ℝ} :
    Set.EqOn (fun t : ℝ => envProfileFree h x y (max (-(x c)) (min (y c) t)))
      (envProfileFree h x y) (Set.Icc (-(x c)) (y c)) := by
  intro t ht
  show envProfileFree h x y (max (-(x c)) (min (y c) t)) = envProfileFree h x y t
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- **Continuity of `(A)` in the slope.** -/
theorem continuousAt_momentA_free {n : ℕ} {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun u : ℝ => Work.OddCurve.momentA n h x y (envProfileFree h x y) u) s := by
  set c₀ : ℝ := s / 2 with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  have hc₀s : c₀ < s := by rw [hc₀def]; linarith
  have hle : -(x c₀) ≤ y c₀ := by
    have h1 := H.pos_x hc₀
    have h2 := H.pos_y hc₀
    linarith
  obtain ⟨g, hgcont, hgeq⟩ :
      ∃ g : ℝ → ℝ, Continuous g ∧ Set.EqOn g (envProfileFree h x y) (Set.Icc (-(x c₀)) (y c₀)) :=
    ⟨fun t => envProfileFree h x y (max (-(x c₀)) (min (y c₀) t)),
      continuous_clamp_envProfileFree H hc₀, clamp_envProfileFree_eqOn⟩
  -- the reparametrisation of the slope
  let b : ContDiffBump (s : ℝ) := ⟨s / 4, s / 2, by linarith, by linarith⟩
  let cc : ℝ → ℝ := fun u => s + (u - s) * (b u)
  let HH : ℝ → ℝ := fun u => h (cc u)
  have hb_cont : ContDiff ℝ ∞ (fun u : ℝ => (b u : ℝ)) := b.contDiff
  have hcc_smooth : ContDiff ℝ ∞ cc := by
    have h1 : ContDiff ℝ ∞ (fun u : ℝ => u - s) := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => (u - s) * (b u : ℝ)) := h1.mul hb_cont
    have h3 : ContDiff ℝ ∞ (fun u : ℝ => s + (u - s) * (b u : ℝ)) := contDiff_const.add h2
    simpa [cc] using h3
  have hcc_self : ∀ u : ℝ, u ∈ Metric.ball s (s / 4) → cc u = u := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
    simp [cc, h1]
  have hccpos : ∀ u : ℝ, 0 < cc u := by
    intro u
    rcases lt_or_ge |u - s| (s / 2) with h | h
    · have hb0 : 0 ≤ b u := b.nonneg
      have hb1 : b u ≤ 1 := b.le_one
      have hle' : |cc u - s| ≤ |u - s| := by
        have h' : cc u - s = (u - s) * b u := by simp [cc]
        rw [h', abs_mul, abs_of_nonneg hb0]
        nlinarith [abs_nonneg (u - s), hb1]
      have hlt : |cc u - s| < s / 2 := lt_of_le_of_lt hle' h
      have := neg_abs_le (cc u - s)
      linarith
    · have hb0 : b u = 0 := b.zero_of_le_dist (by rwa [Real.dist_eq])
      simp [cc, hb0, hs]
  have hHH_smooth : ContDiff ℝ ∞ HH := by
    have hcomp := H.smooth_h.comp (s := Set.univ) (t := Set.Ioi 0) hcc_smooth.contDiffOn
      (fun u _ => hccpos u)
    rw [contDiffOn_univ] at hcomp
    simpa [HH, Function.comp_def] using hcomp
  have hcc_cont : Continuous cc := hcc_smooth.continuous
  have hHH_cont : Continuous HH := hHH_smooth.continuous
  -- joint continuity of the parametric integrand
  have hcontA : Continuous fun p : ℝ × ℝ =>
      (g p.2 ^ 2 - (cc p.1 * p.2 + HH (cc p.1)) ^ 2) ^ n *
        Real.sqrt (g p.2 ^ 2 - (cc p.1 * p.2 + HH (cc p.1)) ^ 2) := by
    fun_prop
  have hparamA : Continuous fun u : ℝ => ∫ t in (-(x c₀))..(y c₀),
      (g t ^ 2 - (cc u * t + HH (cc u)) ^ 2) ^ n *
        Real.sqrt (g t ^ 2 - (cc u * t + HH (cc u)) ^ 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      hcontA (-(x c₀)) (y c₀)
  refine ContinuousAt.congr_of_eventuallyEq
    (g := fun u : ℝ => Work.OddCurve.momentA n h x y (envProfileFree h x y) u)
    hparamA.continuousAt ?_
  filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < s / 4)] with u hu
  have hudist : |u - s| < s / 4 := by
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact hu
  have hc₀u : c₀ < u := by
    rw [abs_lt] at hudist
    rw [hc₀def]
    linarith [hudist.1]
  have hccu : cc u = u := hcc_self u hu
  have hHHu : HH u = h u := by
    simp only [HH, hccu]
  rw [momentA_eq_fixedInterval_free H hc₀ hc₀u.le]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have hgt : g t = envProfileFree h x y t := hgeq ht
  simp only [Work.OddCurve.rad_def, ← hgt, hccu, hHHu]

/-- **Continuity of `(B)` in the slope.** -/
theorem continuousAt_momentB_free {n : ℕ} {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun u : ℝ => Work.OddCurve.momentB n h x y (envProfileFree h x y) u) s := by
  set c₀ : ℝ := s / 2 with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  have hle : -(x c₀) ≤ y c₀ := by
    have h1 := H.pos_x hc₀
    have h2 := H.pos_y hc₀
    linarith
  obtain ⟨g, hgcont, hgeq⟩ :
      ∃ g : ℝ → ℝ, Continuous g ∧ Set.EqOn g (envProfileFree h x y) (Set.Icc (-(x c₀)) (y c₀)) :=
    ⟨fun t => envProfileFree h x y (max (-(x c₀)) (min (y c₀) t)),
      continuous_clamp_envProfileFree H hc₀, clamp_envProfileFree_eqOn⟩
  let b : ContDiffBump (s : ℝ) := ⟨s / 4, s / 2, by linarith, by linarith⟩
  let cc : ℝ → ℝ := fun u => s + (u - s) * (b u)
  let HH : ℝ → ℝ := fun u => h (cc u)
  have hb_cont : ContDiff ℝ ∞ (fun u : ℝ => (b u : ℝ)) := b.contDiff
  have hcc_smooth : ContDiff ℝ ∞ cc := by
    have h1 : ContDiff ℝ ∞ (fun u : ℝ => u - s) := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => (u - s) * (b u : ℝ)) := h1.mul hb_cont
    have h3 : ContDiff ℝ ∞ (fun u : ℝ => s + (u - s) * (b u : ℝ)) := contDiff_const.add h2
    simpa [cc] using h3
  have hcc_self : ∀ u : ℝ, u ∈ Metric.ball s (s / 4) → cc u = u := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
    simp [cc, h1]
  have hccpos : ∀ u : ℝ, 0 < cc u := by
    intro u
    rcases lt_or_ge |u - s| (s / 2) with h | h
    · have hb0 : 0 ≤ b u := b.nonneg
      have hb1 : b u ≤ 1 := b.le_one
      have hle' : |cc u - s| ≤ |u - s| := by
        have h' : cc u - s = (u - s) * b u := by simp [cc]
        rw [h', abs_mul, abs_of_nonneg hb0]
        nlinarith [abs_nonneg (u - s), hb1]
      have hlt : |cc u - s| < s / 2 := lt_of_le_of_lt hle' h
      have := neg_abs_le (cc u - s)
      linarith
    · have hb0 : b u = 0 := b.zero_of_le_dist (by rwa [Real.dist_eq])
      simp [cc, hb0, hs]
  have hHH_smooth : ContDiff ℝ ∞ HH := by
    have hcomp := H.smooth_h.comp (s := Set.univ) (t := Set.Ioi 0) hcc_smooth.contDiffOn
      (fun u _ => hccpos u)
    rw [contDiffOn_univ] at hcomp
    simpa [HH, Function.comp_def] using hcomp
  have hcc_cont : Continuous cc := hcc_smooth.continuous
  have hHH_cont : Continuous HH := hHH_smooth.continuous
  have hdH_cont : Continuous (deriv HH) := hHH_smooth.continuous_deriv (by simp)
  have hcontB : Continuous fun p : ℝ × ℝ =>
      (g p.2 ^ 2 - (cc p.1 * p.2 + HH (cc p.1)) ^ 2) ^ (n - 1) *
        Real.sqrt (g p.2 ^ 2 - (cc p.1 * p.2 + HH (cc p.1)) ^ 2) *
        (p.2 + deriv HH (cc p.1)) := by
    fun_prop
  have hparamB : Continuous fun u : ℝ => ∫ t in (-(x c₀))..(y c₀),
      (g t ^ 2 - (cc u * t + HH (cc u)) ^ 2) ^ (n - 1) *
        Real.sqrt (g t ^ 2 - (cc u * t + HH (cc u)) ^ 2) * (t + deriv HH (cc u)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      hcontB (-(x c₀)) (y c₀)
  refine ContinuousAt.congr_of_eventuallyEq
    (g := fun u : ℝ => Work.OddCurve.momentB n h x y (envProfileFree h x y) u)
    hparamB.continuousAt ?_
  filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < s / 4)] with u hu
  have hudist : |u - s| < s / 4 := by
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact hu
  have hc₀u : c₀ < u := by
    rw [abs_lt] at hudist
    rw [hc₀def]
    linarith [hudist.1]
  have hccu : cc u = u := hcc_self u hu
  have hball : Metric.ball s (s / 4) ∈ 𝓝 u := Metric.isOpen_ball.mem_nhds hu
  have heq : HH =ᶠ[𝓝 u] h := by
    filter_upwards [hball] with v hv
    simp only [HH, hcc_self v hv]
  have hHHu : HH u = h u := heq.self_of_nhds
  have hderiv : deriv HH u = deriv h u := heq.deriv_eq
  rw [momentB_eq_fixedInterval_free H hc₀ hc₀u.le]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have hgt : g t = envProfileFree h x y t := hgeq ht
  simp only [Work.OddCurve.rad_def, ← hgt, hccu, hHHu, hderiv]

end

end Work.OddVolterra.Free
