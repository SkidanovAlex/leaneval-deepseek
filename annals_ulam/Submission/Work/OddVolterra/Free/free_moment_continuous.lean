import Mathlib
import Submission.Work.OddCurve.Free.ChordCurveFree
import Submission.Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free

/-!
# Continuity of the free-tip moment integrals in the cutting slope

`Work.OddCurve.momentA`/`momentB` are integrals over the *moving* section `(-(x s), y s)` of the
integrand built from the untruncated envelope profile.  This file proves that, for a free-tip
envelope curve, both are continuous functions of the slope at every `s > 0`.

The two ingredients are

* `free_profile_continuousOn`: the untruncated envelope profile is continuous on `[A,B]` as soon
  as `[A,B] ⊂ (-rx, ry)`, `rx`/`ry` being the two tips (its branch is `σ t ↦ σ t · t + h σ t`, a
  composition of the continuous inverse slope with the smooth data; at `0` it is the semicircle);
* `Work.OddVolterra.Free.rad_nonpos_outside_free`: the radicand vanishes outside the section, so
  on a *fixed* window `[-(X c), Y c]` (for a slope `c ≤ u`) the integral over the moving section
  equals the integral over the fixed window.

The window and the bump are then localised (`Continuous continuous_clamp_Icc`, and a smooth
reparametrisation of the bump near `s`), which makes the integrand a *globally* continuous
function of `(u,t)` and reduces the claim to the parametric integral lemma.
-/

namespace Work.OddVolterra.Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

variable {h x y : ℝ → ℝ}

/-! ## Continuity of the untruncated envelope profile -/

/-- **The untruncated envelope profile is continuous on `[A,B]` for `[A,B] ⊂ (-rx, ry)`.**

On `(0,ry)` the profile is `envelopeRight h y = σ t ↦ σ t · t + h σ t` with `slopeRight y` the
continuous inverse slope of the strictly decreasing `y` (`IsChordCurveFree.continuousOn_slopeRight`)
and `h` smooth at the positive slope; symmetrically on `(-rx,0)`.  At `t = 0` the two branches are
glued through the semicircle: on `(-tStar, tStar)` the profile *is* the semicircle. -/
theorem free_profile_continuousOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {rx ry : ℝ} (hrx : Filter.Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 rx))
    (hry : Filter.Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 ry))
    {A B : ℝ} (hA : -rx < A) (hB : B < ry) :
    ContinuousOn (envProfileFree h x y) (Set.Icc A B) := by
  have hcx : Work.OddCurve.Free.IsChordCurveFree x := H.toChordCurveFree_x
  have hcy : Work.OddCurve.Free.IsChordCurveFree y := H.toChordCurveFree_y
  have hopen : ContinuousOn (envProfileFree h x y) (Set.Ioo (-rx) ry) := by
    rw [isOpen_Ioo.continuousOn_iff]
    intro t ht
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · -- the left branch
      have hloc : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeLeft h x := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with u hu
        have hu' : u < 0 := hu
        rw [envProfileFree, if_neg (not_lt.mpr hu'.le), if_pos hu']
      have hsl_cont : ContinuousAt (Work.OddEnvelope.slopeLeft x) t :=
        (hcx.continuousOn_slopeLeft hrx).continuousAt
          (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], hneg⟩)
      have hsl_pos : 0 < Work.OddEnvelope.slopeLeft x t :=
        hcx.slopeLeft_pos hrx ⟨ht.1, hneg⟩
      have hcomp : ContinuousAt (fun u : ℝ => h (Work.OddEnvelope.slopeLeft x u)) t :=
        ((H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds hsl_pos)).continuousAt).comp hsl_cont
      have hmain : ContinuousAt (Work.OddEnvelope.envelopeLeft h x) t := by
        unfold Work.OddEnvelope.envelopeLeft
        exact ((hsl_cont.mul continuousAt_id).add hcomp).neg
      exact hmain.congr hloc.symm
    · -- `t = 0`: the semicircle
      rw [heq]
      have hev : envProfileFree h x y =ᶠ[𝓝 (0 : ℝ)] Work.OddEnvelope.semicircle := by
        filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-Work.OddEnvelope.tStar)
            Work.OddEnvelope.tStar from
          ⟨neg_lt_zero.mpr Work.OddEnvelope.tStar_pos, Work.OddEnvelope.tStar_pos⟩)] with u hu
        rcases lt_trichotomy u 0 with hu' | hu' | hu'
        · rw [envProfileFree, if_neg (not_lt.mpr hu'.le), if_pos hu']
          exact Work.OddCurve.Free.envelopeLeft_eq_semicircle_free H ⟨hu.1, hu'⟩
        · rw [hu', envProfileFree, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
          norm_num [Work.OddEnvelope.semicircle]
        · rw [envProfileFree, if_pos hu']
          exact Work.OddCurve.Free.envelopeRight_eq_semicircle_free H ⟨hu', hu.2⟩
      have hsem : ContinuousAt Work.OddEnvelope.semicircle (0 : ℝ) := by
        show ContinuousAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) 0
        exact Real.continuous_sqrt.continuousAt.comp (by fun_prop)
      exact hsem.congr hev.symm
    · -- the right branch
      have hloc : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeRight h y := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with u hu
        have hu' : 0 < u := hu
        rw [envProfileFree, if_pos hu']
      have hsl_cont : ContinuousAt (Work.OddEnvelope.slopeRight y) t :=
        (hcy.continuousOn_slopeRight hry).continuousAt
          (isOpen_Ioo.mem_nhds ⟨hpos, by linarith [ht.2]⟩)
      have hsl_pos : 0 < Work.OddEnvelope.slopeRight y t :=
        hcy.slopeRight_pos hry ⟨hpos, ht.2⟩
      have hcomp : ContinuousAt (fun u : ℝ => h (Work.OddEnvelope.slopeRight y u)) t :=
        ((H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds hsl_pos)).continuousAt).comp hsl_cont
      have hmain : ContinuousAt (Work.OddEnvelope.envelopeRight h y) t := by
        unfold Work.OddEnvelope.envelopeRight
        exact (hsl_cont.mul continuousAt_id).add hcomp
      exact hmain.congr hloc.symm
  exact hopen.mono (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)

/-! ## Clamping -/

/-- **Clamping a function that is continuous on `[A,B]`.**  `t ↦ f (min B (max A t))` is globally
continuous and agrees with `f` on `[A,B]`. -/
theorem continuous_clamp_Icc {f : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hf : ContinuousOn f (Set.Icc A B)) :
    Continuous (fun t : ℝ => f (min B (max A t))) := by
  have hclamp : Continuous (fun t : ℝ => min B (max A t)) :=
    continuous_const.min (continuous_const.max continuous_id)
  exact hf.comp_continuous hclamp
    (fun t => ⟨le_min hAB (le_max_left A t), min_le_left B (max A t)⟩)


/-! ## Continuity of the moment integrals in the slope -/

/-- **`(A)` is continuous in the slope**, free tips.

Take the fixed window `[A,B] = [-(X c), Y c]` with `c = s/2`.  For `u ≥ c` the section lies inside
it, and by `Work.OddVolterra.Free.rad_nonpos_outside_free` the integrand vanishes outside the
section, so the moment integral is the integral over the *fixed* window.  Clamping the profile to
`[A,B]` and reparametrising the bump near `s` makes the integrand a globally continuous function
of `(u,t)`, and the parametric integral lemma gives continuity at `s`. -/
theorem continuousAt_momentA_envProfileFree (n : ℕ) {h X Y : ℝ → ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun u : ℝ => Work.OddCurve.momentA n h X Y (envProfileFree h X Y) u) s := by
  obtain ⟨rx, -, hrx⟩ := hX.x_tendsto_free
  obtain ⟨ry, -, hry⟩ := hX.y_tendsto_free
  have hcx : Work.OddCurve.Free.IsChordCurveFree X := hX.toChordCurveFree_x
  have hcy : Work.OddCurve.Free.IsChordCurveFree Y := hX.toChordCurveFree_y
  -- the fixed window
  set c : ℝ := s / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hclt : c < s := by rw [hcdef]; linarith
  set A : ℝ := -(X c) with hAdef
  set B : ℝ := Y c with hBdef
  have hXcpos : 0 < X c := hcx.pos hcpos
  have hYcpos : 0 < Y c := hcy.pos hcpos
  have hAB : A ≤ B := by rw [hAdef, hBdef]; linarith
  have hAc : -rx < A := by
    rw [hAdef]
    have := hcx.lt_tip hrx hcpos
    linarith
  have hBc : B < ry := by rw [hBdef]; exact hcy.lt_tip hry hcpos
  have hFcont : ContinuousOn (envProfileFree h X Y) (Set.Icc A B) :=
    free_profile_continuousOn hX hrx hry hAc hBc
  -- clamping the profile to the window
  have hFc : Continuous (fun t : ℝ => envProfileFree h X Y (min B (max A t))) :=
    continuous_clamp_Icc hAB hFcont
  have hFeq : ∀ t ∈ Set.Icc A B,
      envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t := by
    intro t ht
    rw [max_eq_right ht.1, min_eq_right ht.2]
  -- the localisation of the bump near `s`
  let bl : ContDiffBump (s : ℝ) := ⟨s / 4, s / 2, by linarith, by linarith⟩
  let ρ : ℝ → ℝ := fun u => s + (u - s) * (bl u)
  let H : ℝ → ℝ := fun u => h (ρ u)
  have hρ_smooth : ContDiff ℝ ∞ ρ := by
    have hb_cont : ContDiff ℝ ∞ (fun u : ℝ => (bl u : ℝ)) := bl.contDiff
    have h1 : ContDiff ℝ ∞ (fun u : ℝ => u - s) := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => (u - s) * (bl u : ℝ)) := h1.mul hb_cont
    have h3 : ContDiff ℝ ∞ (fun u : ℝ => s + (u - s) * (bl u : ℝ)) := contDiff_const.add h2
    simpa [ρ] using h3
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_self : ∀ u : ℝ, u ∈ Metric.ball s (s / 4) → ρ u = u := by
    intro u hu
    have h1 : bl u = 1 := bl.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
    simp [ρ, h1]
  have hρ_pos : ∀ u : ℝ, 0 < ρ u := by
    intro u
    rcases lt_or_ge |u - s| (s / 2) with h | h
    · have hb0 : 0 ≤ bl u := bl.nonneg
      have hb1 : bl u ≤ 1 := bl.le_one
      have hle : |ρ u - s| ≤ |u - s| := by
        have h' : ρ u - s = (u - s) * (bl u : ℝ) := by simp [ρ]
        rw [h', abs_mul, abs_of_nonneg hb0]
        nlinarith [abs_nonneg (u - s), hb1]
      have hlt : |ρ u - s| < s / 2 := lt_of_le_of_lt hle h
      have := neg_abs_le (ρ u - s)
      linarith
    · have hb0 : bl u = 0 := bl.zero_of_le_dist (by rwa [Real.dist_eq])
      simp [ρ, hb0, hs]
  have hH_smooth : ContDiff ℝ ∞ H := by
    have hcomp := hX.smooth_h.comp (s := Set.univ) (t := Set.Ioi 0) hρ_smooth.contDiffOn
      (fun u _ => hρ_pos u)
    rw [contDiffOn_univ] at hcomp
    simpa [H, Function.comp_def] using hcomp
  have hH_cont : Continuous H := hH_smooth.continuous
  -- the continuous expression
  have hcont_int : Continuous fun u : ℝ => ∫ t in A..B,
      (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
        Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) := by
    have h1 : Continuous fun p : ℝ × ℝ => envProfileFree h X Y (min B (max A p.2)) :=
      hFc.comp continuous_snd
    have h2 : Continuous fun p : ℝ × ℝ => ρ p.1 * p.2 + H (ρ p.1) :=
      ((hρ_cont.comp continuous_fst).mul continuous_snd).add
        (hH_cont.comp (hρ_cont.comp continuous_fst))
    have h3 : Continuous fun p : ℝ × ℝ =>
        envProfileFree h X Y (min B (max A p.2)) ^ 2 - (ρ p.1 * p.2 + H (ρ p.1)) ^ 2 :=
      (h1.pow 2).sub (h2.pow 2)
    have h4 : Continuous fun p : ℝ × ℝ =>
        Real.sqrt (envProfileFree h X Y (min B (max A p.2)) ^ 2 -
          (ρ p.1 * p.2 + H (ρ p.1)) ^ 2) :=
      Real.continuous_sqrt.comp h3
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    show Continuous fun p : ℝ × ℝ =>
      (envProfileFree h X Y (min B (max A p.2)) ^ 2 - (ρ p.1 * p.2 + H (ρ p.1)) ^ 2) ^ n *
        Real.sqrt (envProfileFree h X Y (min B (max A p.2)) ^ 2 -
          (ρ p.1 * p.2 + H (ρ p.1)) ^ 2)
    exact (h3.pow n).mul h4
  -- the moment integral is the fixed-window integral near `s`
  have hev : (fun u : ℝ => Work.OddCurve.momentA n h X Y (envProfileFree h X Y) u) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in A..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2)) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < s / 4)] with u hu
    have hdist : dist u s < s / 4 := Metric.mem_ball.mp hu
    have hdist' : |u - s| < s / 4 := by rwa [Real.dist_eq] at hdist
    have hulow : s - s / 4 < u := by
      have := neg_abs_le (u - s); linarith
    have hu_pos : 0 < u := by linarith
    have hρu : ρ u = u := hρ_self u hu
    have hcu : c < u := by rw [hcdef]; linarith
    have hHu : H u = h u := by simp [H, hρu]
    -- section bounds
    have hAu : A ≤ -(X u) := by
      rw [hAdef]
      have := hcx.strictAntiOn hcpos hu_pos hcu
      linarith
    have hBu : Y u ≤ B := by
      rw [hBdef]
      exact (hcy.strictAntiOn hcpos hu_pos hcu).le
    have hXu_pos : 0 < X u := hcx.pos hu_pos
    have hYu_pos : 0 < Y u := hcy.pos hu_pos
    have hsec : -(X u) ≤ Y u := by linarith
    have hrad := Work.OddVolterra.Free.rad_nonpos_outside_free (h := h) (x := X) (y := Y)
      hX hcpos hcu.le
    -- the integrand vanishes on the two outer pieces
    have hzero_left : ∀ t : ℝ, t ∈ Set.Icc A (-(X u)) →
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2)
          = 0 := by
      intro t ht
      have htB : t ≤ B := le_trans (le_trans ht.2 hsec) hBu
      have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
        hFeq t ⟨ht.1, htB⟩
      have hrad_t : Work.OddCurve.rad h (envProfileFree h X Y) u t ≤ 0 :=
        hrad.2 t (by simpa [hAdef] using ht.1) ht.2
      rw [Work.OddCurve.rad_def] at hrad_t
      have hle : envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2 ≤ 0 := by
        rw [hFt, hρu, hHu]
        exact hrad_t
      rw [Real.sqrt_eq_zero_of_nonpos hle, mul_zero]
    have hzero_right : ∀ t : ℝ, t ∈ Set.Icc (Y u) B →
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2)
          = 0 := by
      intro t ht
      have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
        hFeq t ⟨le_trans hAu (le_trans hsec ht.1), ht.2⟩
      have hrad_t : Work.OddCurve.rad h (envProfileFree h X Y) u t ≤ 0 :=
        hrad.1 t ht.1 (by simpa [hBdef] using ht.2)
      rw [Work.OddCurve.rad_def] at hrad_t
      have hle : envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2 ≤ 0 := by
        rw [hFt, hρu, hHu]
        exact hrad_t
      rw [Real.sqrt_eq_zero_of_nonpos hle, mul_zero]
    have hInt : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ =>
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2)) volume p q := by
      intro p q
      apply Continuous.intervalIntegrable
      fun_prop
    have hzb : (∫ t in A..(-(X u)),
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2)) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_).trans ?_
      · intro t ht
        rw [Set.uIcc_of_le hAu] at ht
        exact hzero_left t ht
      · simp
    have hza : (∫ t in (Y u)..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2)) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_).trans ?_
      · intro t ht
        rw [Set.uIcc_of_le hBu] at ht
        exact hzero_right t ht
      · simp
    have hsplit : (∫ t in A..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2))
        = ∫ t in (-(X u))..(Y u),
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt A (-(X u))) (hInt (-(X u)) B),
        hzb, zero_add]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (-(X u)) (Y u)) (hInt (Y u) B)]
      rw [hza, add_zero]
    calc Work.OddCurve.momentA n h X Y (envProfileFree h X Y) u
        = ∫ t in (-(X u))..(Y u), (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) ^ n *
            Real.sqrt (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) := by
          rw [Work.OddCurve.momentA_def]
          simp only [Work.OddCurve.rad_def]
      _ = ∫ t in (-(X u))..(Y u),
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hsec] at ht
          have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
            hFeq t ⟨le_trans hAu ht.1, le_trans ht.2 hBu⟩
          have hlin : ρ u * t + H (ρ u) = u * t + h u := by rw [hρu, hHu]
          change (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) ^ n *
              Real.sqrt (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) =
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2)
          rw [hFt, hlin]
      _ = ∫ t in A..B,
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ n *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2) := hsplit.symm
  exact hcont_int.continuousAt.congr hev.symm


/-- **`(B)` is continuous in the slope**, free tips.  Same proof as `(A)`, with the extra factor
`t + h' u` in the integrand (carried through the localisation as `t + deriv H (ρ u)`). -/
theorem continuousAt_momentB_envProfileFree (n : ℕ) {h X Y : ℝ → ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun u : ℝ => Work.OddCurve.momentB n h X Y (envProfileFree h X Y) u) s := by
  obtain ⟨rx, -, hrx⟩ := hX.x_tendsto_free
  obtain ⟨ry, -, hry⟩ := hX.y_tendsto_free
  have hcx : Work.OddCurve.Free.IsChordCurveFree X := hX.toChordCurveFree_x
  have hcy : Work.OddCurve.Free.IsChordCurveFree Y := hX.toChordCurveFree_y
  set c : ℝ := s / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  set A : ℝ := -(X c) with hAdef
  set B : ℝ := Y c with hBdef
  have hXcpos : 0 < X c := hcx.pos hcpos
  have hYcpos : 0 < Y c := hcy.pos hcpos
  have hAB : A ≤ B := by rw [hAdef, hBdef]; linarith
  have hAc : -rx < A := by
    rw [hAdef]
    have := hcx.lt_tip hrx hcpos
    linarith
  have hBc : B < ry := by rw [hBdef]; exact hcy.lt_tip hry hcpos
  have hFcont : ContinuousOn (envProfileFree h X Y) (Set.Icc A B) :=
    free_profile_continuousOn hX hrx hry hAc hBc
  have hFc : Continuous (fun t : ℝ => envProfileFree h X Y (min B (max A t))) :=
    continuous_clamp_Icc hAB hFcont
  have hFeq : ∀ t ∈ Set.Icc A B,
      envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t := by
    intro t ht
    rw [max_eq_right ht.1, min_eq_right ht.2]
  let bl : ContDiffBump (s : ℝ) := ⟨s / 4, s / 2, by linarith, by linarith⟩
  let ρ : ℝ → ℝ := fun u => s + (u - s) * (bl u)
  let H : ℝ → ℝ := fun u => h (ρ u)
  have hρ_smooth : ContDiff ℝ ∞ ρ := by
    have hb_cont : ContDiff ℝ ∞ (fun u : ℝ => (bl u : ℝ)) := bl.contDiff
    have h1 : ContDiff ℝ ∞ (fun u : ℝ => u - s) := contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => (u - s) * (bl u : ℝ)) := h1.mul hb_cont
    have h3 : ContDiff ℝ ∞ (fun u : ℝ => s + (u - s) * (bl u : ℝ)) := contDiff_const.add h2
    simpa [ρ] using h3
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_self : ∀ u : ℝ, u ∈ Metric.ball s (s / 4) → ρ u = u := by
    intro u hu
    have h1 : bl u = 1 := bl.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
    simp [ρ, h1]
  have hρ_pos : ∀ u : ℝ, 0 < ρ u := by
    intro u
    rcases lt_or_ge |u - s| (s / 2) with h | h
    · have hb0 : 0 ≤ bl u := bl.nonneg
      have hb1 : bl u ≤ 1 := bl.le_one
      have hle : |ρ u - s| ≤ |u - s| := by
        have h' : ρ u - s = (u - s) * (bl u : ℝ) := by simp [ρ]
        rw [h', abs_mul, abs_of_nonneg hb0]
        nlinarith [abs_nonneg (u - s), hb1]
      have hlt : |ρ u - s| < s / 2 := lt_of_le_of_lt hle h
      have := neg_abs_le (ρ u - s)
      linarith
    · have hb0 : bl u = 0 := bl.zero_of_le_dist (by rwa [Real.dist_eq])
      simp [ρ, hb0, hs]
  have hH_smooth : ContDiff ℝ ∞ H := by
    have hcomp := hX.smooth_h.comp (s := Set.univ) (t := Set.Ioi 0) hρ_smooth.contDiffOn
      (fun u _ => hρ_pos u)
    rw [contDiffOn_univ] at hcomp
    simpa [H, Function.comp_def] using hcomp
  have hH_cont : Continuous H := hH_smooth.continuous
  have hdHcont : Continuous (deriv H) := hH_smooth.continuous_deriv (by simp)
  have hcont_int : Continuous fun u : ℝ => ∫ t in A..B,
      (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
        Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) *
        (t + deriv H (ρ u)) := by
    have h1 : Continuous fun p : ℝ × ℝ => envProfileFree h X Y (min B (max A p.2)) :=
      hFc.comp continuous_snd
    have h2 : Continuous fun p : ℝ × ℝ => ρ p.1 * p.2 + H (ρ p.1) :=
      ((hρ_cont.comp continuous_fst).mul continuous_snd).add
        (hH_cont.comp (hρ_cont.comp continuous_fst))
    have h3 : Continuous fun p : ℝ × ℝ =>
        envProfileFree h X Y (min B (max A p.2)) ^ 2 - (ρ p.1 * p.2 + H (ρ p.1)) ^ 2 :=
      (h1.pow 2).sub (h2.pow 2)
    have h4 : Continuous fun p : ℝ × ℝ =>
        Real.sqrt (envProfileFree h X Y (min B (max A p.2)) ^ 2 -
          (ρ p.1 * p.2 + H (ρ p.1)) ^ 2) :=
      Real.continuous_sqrt.comp h3
    have h5 : Continuous fun p : ℝ × ℝ => p.2 + deriv H (ρ p.1) :=
      continuous_snd.add (hdHcont.comp (hρ_cont.comp continuous_fst))
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    show Continuous fun p : ℝ × ℝ =>
      (envProfileFree h X Y (min B (max A p.2)) ^ 2 - (ρ p.1 * p.2 + H (ρ p.1)) ^ 2) ^ (n - 1) *
        Real.sqrt (envProfileFree h X Y (min B (max A p.2)) ^ 2 -
          (ρ p.1 * p.2 + H (ρ p.1)) ^ 2) * (p.2 + deriv H (ρ p.1))
    exact ((h3.pow (n - 1)).mul h4).mul h5
  have hev : (fun u : ℝ => Work.OddCurve.momentB n h X Y (envProfileFree h X Y) u) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in A..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) *
          (t + deriv H (ρ u))) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < s / 4)] with u hu
    have hdist : dist u s < s / 4 := Metric.mem_ball.mp hu
    have hdist' : |u - s| < s / 4 := by rwa [Real.dist_eq] at hdist
    have hulow : s - s / 4 < u := by
      have := neg_abs_le (u - s); linarith
    have hu_pos : 0 < u := by linarith
    have hρu : ρ u = u := hρ_self u hu
    have hcu : c < u := by rw [hcdef]; linarith
    have hHu : H u = h u := by simp [H, hρu]
    have hdHu : deriv H (ρ u) = deriv h u := by
      rw [hρu]
      have hball : Metric.ball s (s / 4) ∈ 𝓝 u := Metric.isOpen_ball.mem_nhds hu
      have heqev : H =ᶠ[𝓝 u] h := by
        filter_upwards [hball] with v hv
        simp [H, hρ_self v hv]
      exact heqev.deriv_eq
    have hAu : A ≤ -(X u) := by
      rw [hAdef]
      have := hcx.strictAntiOn hcpos hu_pos hcu
      linarith
    have hBu : Y u ≤ B := by
      rw [hBdef]
      exact (hcy.strictAntiOn hcpos hu_pos hcu).le
    have hXu_pos : 0 < X u := hcx.pos hu_pos
    have hYu_pos : 0 < Y u := hcy.pos hu_pos
    have hsec : -(X u) ≤ Y u := by linarith
    have hrad := Work.OddVolterra.Free.rad_nonpos_outside_free (h := h) (x := X) (y := Y)
      hX hcpos hcu.le
    have hzero_left : ∀ t : ℝ, t ∈ Set.Icc A (-(X u)) →
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) *
          (t + deriv H (ρ u)) = 0 := by
      intro t ht
      have htB : t ≤ B := le_trans (le_trans ht.2 hsec) hBu
      have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
        hFeq t ⟨ht.1, htB⟩
      have hrad_t : Work.OddCurve.rad h (envProfileFree h X Y) u t ≤ 0 :=
        hrad.2 t (by simpa [hAdef] using ht.1) ht.2
      rw [Work.OddCurve.rad_def] at hrad_t
      have hle : envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2 ≤ 0 := by
        rw [hFt, hρu, hHu]
        exact hrad_t
      rw [Real.sqrt_eq_zero_of_nonpos hle]
      ring
    have hzero_right : ∀ t : ℝ, t ∈ Set.Icc (Y u) B →
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) *
          (t + deriv H (ρ u)) = 0 := by
      intro t ht
      have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
        hFeq t ⟨le_trans hAu (le_trans hsec ht.1), ht.2⟩
      have hrad_t : Work.OddCurve.rad h (envProfileFree h X Y) u t ≤ 0 :=
        hrad.1 t ht.1 (by simpa [hBdef] using ht.2)
      rw [Work.OddCurve.rad_def] at hrad_t
      have hle : envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2 ≤ 0 := by
        rw [hFt, hρu, hHu]
        exact hrad_t
      rw [Real.sqrt_eq_zero_of_nonpos hle]
      ring
    have hInt : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ =>
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u))) volume p q := by
      intro p q
      apply Continuous.intervalIntegrable
      have h1 : Continuous fun t : ℝ => envProfileFree h X Y (min B (max A t)) := hFc
      have h2 : Continuous fun t : ℝ => (ρ u * t + H (ρ u)) :=
        (continuous_const.mul continuous_id).add continuous_const
      have h3 : Continuous fun t : ℝ =>
          envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2 :=
        (h1.pow 2).sub (h2.pow 2)
      have h4 : Continuous fun t : ℝ => Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
        (ρ u * t + H (ρ u)) ^ 2) := Real.continuous_sqrt.comp h3
      exact ((h3.pow (n - 1)).mul h4).mul (continuous_id.add continuous_const)
    have hzb : (∫ t in A..(-(X u)),
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u))) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_).trans ?_
      · intro t ht
        rw [Set.uIcc_of_le hAu] at ht
        exact hzero_left t ht
      · simp
    have hza : (∫ t in (Y u)..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u))) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_).trans ?_
      · intro t ht
        rw [Set.uIcc_of_le hBu] at ht
        exact hzero_right t ht
      · simp
    have hsplit : (∫ t in A..B,
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u)))
        = ∫ t in (-(X u))..(Y u),
        (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
          Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
            (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u)) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt A (-(X u))) (hInt (-(X u)) B),
        hzb, zero_add]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (-(X u)) (Y u)) (hInt (Y u) B)]
      rw [hza, add_zero]
    calc Work.OddCurve.momentB n h X Y (envProfileFree h X Y) u
        = ∫ t in (-(X u))..(Y u), (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) *
            Real.sqrt (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) * (t + deriv h u) := by
          rw [Work.OddCurve.momentB_def]
          simp only [Work.OddCurve.rad_def]
      _ = ∫ t in (-(X u))..(Y u),
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hsec] at ht
          have hFt : envProfileFree h X Y (min B (max A t)) = envProfileFree h X Y t :=
            hFeq t ⟨le_trans hAu ht.1, le_trans ht.2 hBu⟩
          have hlin : ρ u * t + H (ρ u) = u * t + h u := by rw [hρu, hHu]
          change (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) *
              Real.sqrt (envProfileFree h X Y t ^ 2 - (u * t + h u) ^ 2) * (t + deriv h u) =
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u))
          rw [hFt, hlin, hdHu]
      _ = ∫ t in A..B,
            (envProfileFree h X Y (min B (max A t)) ^ 2 - (ρ u * t + H (ρ u)) ^ 2) ^ (n - 1) *
              Real.sqrt (envProfileFree h X Y (min B (max A t)) ^ 2 -
                (ρ u * t + H (ρ u)) ^ 2) * (t + deriv H (ρ u)) := hsplit.symm
  exact hcont_int.continuousAt.congr hev.symm

end

end Work.OddVolterra.Free
