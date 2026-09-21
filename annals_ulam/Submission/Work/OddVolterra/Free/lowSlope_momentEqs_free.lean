import Mathlib
import Submission.Work.OddCurve.LowSlope.reduction
import Submission.Work.OddCurve.LowSlope.cl1
import Submission.Work.OddCurve.hasDerivAt_momentA
import Submission.Work.OddCurve.hasDerivAt_integral_rad_general
import Submission.Work.OddCurve.rad_nonpos_outside
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free
import Submission.Work.OddVolterra.Free.free_profile_continuity
import Submission.Work.OddVolterra.Free.free_moment_continuity
import Submission.Work.OddCurve.Free.ChordCurveFree

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

private lemma clamp_mem_Icc' {a b t : ℝ} (hab : a ≤ b) : max a (min b t) ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private lemma sqrt_cube (u : ℝ) :
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = Real.sqrt (1 + u ^ 2) ^ 3 := by
  have h : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  calc (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)
      = Real.sqrt (1 + u ^ 2) ^ 2 * Real.sqrt (1 + u ^ 2) := by rw [h]
    _ = Real.sqrt (1 + u ^ 2) ^ 3 := by ring

/-- **The Leibniz rule for the odd moment integrand, `ContinuousOn` version.**

`Work.OddCurve.hasDerivAt_integral_rad_general` with the hypothesis `Continuous f` replaced by
`ContinuousOn f (Set.Icc a b)`.  The proof replaces `f` by its *flat continuous extension*
`t ↦ f (max a (min b t))` (continuous because the clamp is continuous and lands in `Icc a b`),
which agrees with `f` on `[a,b]`; both the integrand and the derivative kernel are functions of
`t` through `f t` alone, so the two interval integrals — of the integrand for every slope `u`, and
of the kernel at `s` — are unchanged.  `Work.OddCurve.hasDerivAt_integral_rad_general` applied to
the extension then gives the claim. -/
theorem hasDerivAt_integral_rad_continuousOn {n : ℕ} (hn : 1 ≤ n) {h f : ℝ → ℝ} {a b s : ℝ}
    (hab : a ≤ b) (hh : ∀ᶠ u in nhds s, DifferentiableAt ℝ h u)
    (hf : ContinuousOn f (Set.Icc a b)) :
    HasDerivAt (fun u : ℝ => ∫ t in a..b,
        Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t))
      (∫ t in a..b, -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t)) s := by
  set g : ℝ → ℝ := fun t => f (max a (min b t)) with hg
  have hgcont : Continuous g := by
    have h1 : Continuous fun t : ℝ => max a (min b t) := by fun_prop
    have h2 : Continuous (f ∘ fun t : ℝ => max a (min b t)) :=
      hf.comp_continuous h1 (fun t => clamp_mem_Icc' hab)
    simpa only [hg, Function.comp_def] using h2
  have hgen := Work.OddCurve.hasDerivAt_integral_rad_general (n := n) (h := h) (f := g)
    (a := a) (b := b) (s := s) hn hab hh hgcont
  have hval : ∀ t ∈ Set.uIcc a b, g t = f t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [hg, min_eq_right ht.2, max_eq_right ht.1]
  have hLHS : ∀ u : ℝ, (∫ t in a..b,
        Work.OddCurve.rad h g u t ^ n * Real.sqrt (Work.OddCurve.rad h g u t))
      = ∫ t in a..b,
        Work.OddCurve.rad h f u t ^ n * Real.sqrt (Work.OddCurve.rad h f u t) := by
    intro u
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Work.OddCurve.rad_def, Work.OddCurve.rad_def, hval t ht]
  have hKER : (∫ t in a..b, -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h g s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h g s t))
      = ∫ t in a..b, -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Work.OddCurve.rad_def, Work.OddCurve.rad_def, hval t ht]
  exact (hgen.congr_deriv hKER).congr_of_eventuallyEq
    (Eventually.of_forall fun u => (hLHS u).symm)

/-- **The moment integral `(A)` of the odd case is differentiable in the slope**, free tips.

This is `Work.OddCurve.hasDerivAt_momentA` with `Work.OddEnvelope.IsEnvelopeCurve` replaced by
`Work.OddCurve.Free.IsEnvelopeCurveFree` and `Work.OddEnvelope.envelopeProfile` by
`envProfileFree`.  Since for free tips the profile vanishes outside `[-1,1]` only on the *bands*
between the two sections, the fixed interval used here is `[-(x c), y c]` with `c = s/2`, and the
kernel is transported to the cut section `[-(x s), y s]` with the two-sided
`intervalIntegral_eq_of_eq_zero_between`.

The fixed-interval integral is differentiated with `hasDerivAt_integral_rad_continuousOn` applied
to the *clamped* profile `t ↦ envProfileFree h x y (max (-(x c)) (min (y c) t))`, which is
globally continuous and agrees with the profile on `[-(x c), y c]`
(`Work.OddVolterra.Free.continuous_clamp_envProfileFree`, `...clamp_envProfileFree_eqOn`). -/
theorem hasDerivAt_momentA_free {n : ℕ} (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun u : ℝ => Work.OddCurve.momentA n h x y (envProfileFree h x y) u)
      (∫ t in (-(x s))..(y s),
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t)) s := by
  set c : ℝ := s / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hcs : c < s := by rw [hcdef]; linarith
  have hle : -(x c) ≤ y c := by
    have h1 := H.pos_x hc
    have h2 := H.pos_y hc
    linarith
  -- `h` is differentiable on a neighbourhood of `s` (it is smooth on `(0,∞)` and `s > 0`).
  have hh : ∀ᶠ u : ℝ in nhds s, DifferentiableAt ℝ h u := by
    have hd : DifferentiableOn ℝ h (Set.Ioi (0 : ℝ)) :=
      H.smooth_h.differentiableOn (by simp)
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    exact hd.differentiableAt (isOpen_Ioi.mem_nhds hu)
  -- The clamped profile: globally continuous, equal to the profile on the fixed interval.
  set g : ℝ → ℝ := fun t => envProfileFree h x y (max (-(x c)) (min (y c) t)) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    exact continuous_clamp_envProfileFree H hc
  have hgeq : ∀ t ∈ Set.Icc (-(x c)) (y c), g t = envProfileFree h x y t := by
    intro t ht
    rw [hgdef]
    exact clamp_envProfileFree_eqOn ht
  -- Differentiate the fixed-interval integral of the clamped profile.
  have hgen := hasDerivAt_integral_rad_continuousOn (n := n) (h := h) (f := g)
    (a := -(x c)) (b := y c) (s := s) hn hle hh hgcont.continuousOn
  -- Transfer the clamped profile back to the envelope profile on the interval.
  have hcongr : ∀ u : ℝ, (∫ t in (-(x c))..(y c), Work.OddCurve.rad h g u t ^ n *
        Real.sqrt (Work.OddCurve.rad h g u t))
      = ∫ t in (-(x c))..(y c), Work.OddCurve.rad h (envProfileFree h x y) u t ^ n *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t) := by
    intro u
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hle] at ht
    rw [Work.OddCurve.rad_def, Work.OddCurve.rad_def, hgeq t ht]
  have hKER : (∫ t in (-(x c))..(y c), -(2 * (n : ℝ) + 1) * (s * t + h s) *
        (t + deriv h s) * Work.OddCurve.rad h g s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h g s t))
      = ∫ t in (-(x c))..(y c), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hle] at ht
    rw [Work.OddCurve.rad_def, Work.OddCurve.rad_def, hgeq t ht]
  -- The kernel vanishes on the two bands outside the cut section.
  have hzeroL : ∀ t : ℝ, -(x c) ≤ t → t ≤ -(x s) →
      -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t) = 0 := by
    intro t ht1 ht2
    have hrad := (rad_nonpos_outside_free H hc hcs.le).2 t ht1 ht2
    rw [Real.sqrt_eq_zero_of_nonpos hrad, mul_zero]
  have hzeroR : ∀ t : ℝ, y s ≤ t → t ≤ y c →
      -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t) = 0 := by
    intro t ht1 ht2
    have hrad := (rad_nonpos_outside_free H hc hcs.le).1 t ht1 ht2
    rw [Real.sqrt_eq_zero_of_nonpos hrad, mul_zero]
  have hxcs : x s < x c := H.strictAntiOn_x hc hs hcs
  have hycs : y s < y c := H.strictAntiOn_y hc hs hcs
  have hle1 : -(x c) ≤ -(x s) := by linarith
  have hle2 : -(x s) ≤ y s := by
    have h1 := H.pos_x hs
    have h2 := H.pos_y hs
    linarith
  have htrans : (∫ t in (-(x c))..(y c), -(2 * (n : ℝ) + 1) * (s * t + h s) *
        (t + deriv h s) * Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t))
      = ∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t) :=
    intervalIntegral_eq_of_eq_zero_between (f := fun t : ℝ => -(2 * (n : ℝ) + 1) *
        (s * t + h s) * (t + deriv h s) * Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t))
      hle1 hle2 hycs.le hzeroL hzeroR
  have hmain : HasDerivAt
      (fun u : ℝ => ∫ t in (-(x c))..(y c), Work.OddCurve.rad h (envProfileFree h x y) u t ^ n *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) u t))
      (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t)) s :=
    ((hgen.congr_deriv hKER).congr_of_eventuallyEq
      (Eventually.of_forall fun u => (hcongr u).symm)).congr_deriv htrans
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hcs] with u hu
  exact momentA_eq_fixedInterval_free H hc hu.le

/-- **`cl1` (Ryabogin's Lemma 4.2, converse direction), free-tip envelope form.**

This is `Work.OddCurve.LowSlope.cl1` with `Work.OddEnvelope.IsEnvelopeCurve` replaced by
`Work.OddCurve.Free.IsEnvelopeCurveFree` and `Work.OddEnvelope.envelopeProfile` by
`envProfileFree`.  The port replaces the only two uses of the old interface there —
`Work.OddCurve.continuous_envelopeProfile H` (only for the integrability of the two pieces of the
split kernel on the cut section) and `Work.OddCurve.hasDerivAt_momentA hn H` — by the
`ContinuousOn` continuity `Work.OddVolterra.Free.continuousOn_envProfileFree` on a slightly larger
section `[-(x (s/2)), y (s/2)]` and by `hasDerivAt_momentA_free`.

Everything else is the paper's argument, verbatim: the derivative of `(A)` is
`-(2n+1) ∫ (s t + h s)(t + h'(s)) ψ^{n-1/2}`, the pointwise identity
`(s t + c)(t + d) = s (t + d)² + (c - s d)(t + d)` converts the right-hand side into
`-(2n+1) s ∫ (t + h')² ψ^{n-1/2}`, which `(i1)` evaluates as the derivative of
`(2n+1) c' / √(1+s²)`; hence `(A) - (2n+1)c'/√(1+s²)` is constant on the range, and its value at
the single slope `b` is `0`. -/
theorem cl1_free (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {c' : ℝ}
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h x y (envProfileFree h x y) s = 0)
    (hI1 : ∀ s ∈ Set.Icc a b,
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
          Work.OddCurve.rad h (envProfileFree h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (envProfileFree h x y) s t)) = c')
    (hval : Work.OddCurve.momentA n h x y (envProfileFree h x y) b =
      ((2 * (n : ℝ) + 1) * c') / Real.sqrt (1 + b ^ 2)) :
    ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h x y (envProfileFree h x y) s =
        ((2 * (n : ℝ) + 1) * c') / Real.sqrt (1 + s ^ 2) := by
  set F : ℝ → ℝ := envProfileFree h x y with hF
  set K : ℝ := (2 * (n : ℝ) + 1) * c' with hK
  -- The key step: `momentA - K/√(1+u²)` has vanishing derivative on the range.
  have key : ∀ s ∈ Set.Icc a b,
      HasDerivAt (fun u : ℝ => Work.OddCurve.momentA n h x y F u - K / Real.sqrt (1 + u ^ 2))
        0 s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hD : ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≠ 0 := by positivity
    have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
    -- Continuity of the profile on the cut section, from a slightly larger section.
    set c₀ : ℝ := s / 2 with hc₀def
    have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
    have hc₀s : c₀ < s := by rw [hc₀def]; linarith
    have hxs : x s < x c₀ := H.strictAntiOn_x hc₀ hs0 hc₀s
    have hys : y s < y c₀ := H.strictAntiOn_y hc₀ hs0 hc₀s
    have hsub : Set.Icc (-(x s)) (y s) ⊆ Set.Icc (-(x c₀)) (y c₀) :=
      fun t ht => ⟨by linarith [ht.1], le_trans ht.2 hys.le⟩
    have hFcont : ContinuousOn F (Set.Icc (-(x s)) (y s)) := by
      rw [hF]
      exact (continuousOn_envProfileFree H hc₀).mono hsub
    -- continuity of the radicand and of its half-integer power on the cut section
    have hrad_cont : ContinuousOn (fun t : ℝ => Work.OddCurve.rad h F s t)
        (Set.Icc (-(x s)) (y s)) := by
      have h1 : ContinuousOn (fun t : ℝ => F t ^ 2) (Set.Icc (-(x s)) (y s)) := hFcont.pow 2
      have h2 : ContinuousOn (fun t : ℝ => (s * t + h s) ^ 2) (Set.Icc (-(x s)) (y s)) :=
        (((continuous_const.mul continuous_id).add continuous_const).pow 2).continuousOn
      have h3 : ContinuousOn (fun t : ℝ => F t ^ 2 - (s * t + h s) ^ 2)
          (Set.Icc (-(x s)) (y s)) := h1.sub h2
      simpa only [Work.OddCurve.rad] using h3
    have hAc : ContinuousOn (fun t : ℝ => Work.OddCurve.rad h F s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h F s t)) (Set.Icc (-(x s)) (y s)) :=
      (hrad_cont.pow (n - 1)).mul (Real.continuous_sqrt.comp_continuousOn hrad_cont)
    have hAc' : ContinuousOn (fun t : ℝ => (t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h F s t)) (Set.Icc (-(x s)) (y s)) :=
      (((continuous_id.add continuous_const).pow 2).continuousOn.mul
        (hrad_cont.pow (n - 1))).mul (Real.continuous_sqrt.comp_continuousOn hrad_cont)
    have hle_s : -(x s) ≤ y s := by
      have h1 := H.pos_x hs0
      have h2 := H.pos_y hs0
      linarith
    -- the derivative of the moment integral, and integrability of the two pieces of the split
    have hA : HasDerivAt (fun u : ℝ => Work.OddCurve.momentA n h x y F u)
        (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h F s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h F s t)) s := by
      simpa only [hF] using hasDerivAt_momentA_free (n := n) hn H hs0
    have hf1 : IntervalIntegrable (fun t : ℝ => s * ((t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))
        volume (-(x s)) (y s) :=
      (continuous_const.continuousOn.mul hAc').intervalIntegrable_of_Icc hle_s
    have hf2 : IntervalIntegrable (fun t : ℝ => (h s - s * deriv h s) * ((t + deriv h s) *
        (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))))
        volume (-(x s)) (y s) :=
      (continuous_const.continuousOn.mul (((continuous_id.add continuous_const).continuousOn).mul hAc)
        ).intervalIntegrable_of_Icc hle_s
    -- the algebraic split of the integral
    have hsplit : (∫ t in (-(x s))..(y s), (s * t + h s) * (t + deriv h s) *
          (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))
        = s * (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
            Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
          + (h s - s * deriv h s) * (∫ t in (-(x s))..(y s), (t + deriv h s) *
            (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add hf1 hf2]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [Pi.add_apply]
      ring
    -- the values of the two pieces
    have hJD : (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
            Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) *
          ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) = c' := by
      have h1 := hI1 s hs
      rw [← mul_comm (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
        ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))] at h1
      exact h1
    have hval2 : (∫ t in (-(x s))..(y s), (t + deriv h s) *
            (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))) = 0 := by
      have h1 := hB s hs
      rw [Work.OddCurve.momentB] at h1
      rw [← h1]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have hvalI : (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) *
          (t + deriv h s) * Work.OddCurve.rad h F s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h F s t))
        = -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) := by
      have hstep : (fun t : ℝ => -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
            Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
          = (fun t : ℝ => (-(2 * (n : ℝ) + 1)) * ((s * t + h s) * (t + deriv h s) *
            (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))) := by
        funext t; ring
      rw [hstep, intervalIntegral.integral_const_mul, hsplit, hval2, hK, mul_zero, add_zero,
        ← neg_div, eq_div_iff hD]
      rw [show -(2 * (n : ℝ) + 1) * (s * (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
            Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))) *
            ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))
          = -(2 * (n : ℝ) + 1) * s * ((∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
            Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) *
            ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) by ring]
      rw [hJD]
      ring
    have hN : HasDerivAt (fun u : ℝ => K / Real.sqrt (1 + u ^ 2))
        (-(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)))) s := by
      have hnum : HasDerivAt (fun _ : ℝ => K) 0 s := hasDerivAt_const s K
      have hden : HasDerivAt (fun u : ℝ => Real.sqrt (1 + u ^ 2))
          (s / Real.sqrt (1 + s ^ 2)) s := by
        have h2 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * s) s := by
          have hh : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (0 + 2 * s ^ (2 - 1) * 1) s :=
            (hasDerivAt_const (x := s) (c := (1 : ℝ))).add ((hasDerivAt_id s).pow 2)
          simpa using hh
        have h3 := h2.sqrt (by positivity : (1 : ℝ) + s ^ 2 ≠ 0)
        convert h3 using 1
        field_simp
      have h4 : HasDerivAt (fun u : ℝ => K / Real.sqrt (1 + u ^ 2))
          ((0 * Real.sqrt (1 + s ^ 2) - K * (s / Real.sqrt (1 + s ^ 2))) /
            Real.sqrt (1 + s ^ 2) ^ 2) s :=
        hnum.div hden hne
      have hval_eq : (0 * Real.sqrt (1 + s ^ 2) - K * (s / Real.sqrt (1 + s ^ 2))) /
            Real.sqrt (1 + s ^ 2) ^ 2
          = -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) := by
        rw [sqrt_cube s]
        field_simp
        ring
      rw [hval_eq] at h4
      exact h4
    have hsum := hA.sub hN
    have hval0 : -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) -
        (-(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)))) = 0 := sub_self _
    rw [hvalI, hval0] at hsum
    exact hsum
  -- The fundamental theorem of calculus on the range.
  have main : ∀ s ∈ Set.Icc a b,
      (∫ u in a..s, (0 : ℝ)) = (Work.OddCurve.momentA n h x y F s - K / Real.sqrt (1 + s ^ 2))
        - (Work.OddCurve.momentA n h x y F a - K / Real.sqrt (1 + a ^ 2)) := by
    intro s hs
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => Work.OddCurve.momentA n h x y F u - K / Real.sqrt (1 + u ^ 2))
      (f' := fun _ : ℝ => (0 : ℝ)) ?_ ?_
    · intro u hu
      rw [Set.uIcc_of_le hs.1] at hu
      exact key u ⟨hu.1, le_trans hu.2 hs.2⟩
    · exact intervalIntegrable_const
  have hb0 : Work.OddCurve.momentA n h x y F b - K / Real.sqrt (1 + b ^ 2) = 0 := by
    rw [hval, hK]; ring
  have ha0 : Work.OddCurve.momentA n h x y F a - K / Real.sqrt (1 + a ^ 2) = 0 := by
    have hmain := main b ⟨hab, le_refl b⟩
    rw [intervalIntegral.integral_zero, hb0, zero_sub] at hmain
    linarith
  intro s hs
  have hmain := main s hs
  rw [intervalIntegral.integral_zero, ha0, sub_zero] at hmain
  have h2 : Work.OddCurve.momentA n h x y F s - K / Real.sqrt (1 + s ^ 2) = 0 := hmain.symm
  rw [hK] at h2 ⊢
  exact sub_eq_zero.mp h2

/-- **The low-slope moment equations for the free-tip envelope profile.**

This is `Work.OddCurve.LowSlope.lowSlope_momentEqs`
(`Submission/Work/OddCurve/LowSlope/reduction.lean`, proved; it consumes
`Work.OddCurve.LowSlope.cl1` from `LowSlope/cl1.lean`) with `Work.OddEnvelope.IsEnvelopeCurve`
replaced by `Work.OddCurve.Free.IsEnvelopeCurveFree` and `Work.OddEnvelope.envelopeProfile` by
`Work.OddVolterra.Free.envProfileFree`.  The free-tip curve need not have its tips at `±1`; the
profile is the untruncated envelope, which may be non-zero past `1`.

The port goes through the free-tip `cl1`, `Work.OddVolterra.Free.cl1_free` above (built on
`Work.OddVolterra.Free.hasDerivAt_momentA_free`), which replaces the two uses of the tip
normalisation in `Work.OddCurve.LowSlope.cl1` — `Work.OddCurve.continuous_envelopeProfile H` (for
the integrability of the split kernel on the cut chord) and `Work.OddCurve.hasDerivAt_momentA hn H`
— by the `ContinuousOn` continuity on a slightly larger section
(`Work.OddVolterra.Free.continuousOn_envProfileFree`, used only through
`Work.OddVolterra.Free.rad_nonpos_outside_free`) and by the free Leibniz rule
(`Work.OddVolterra.Free.hasDerivAt_integral_rad_continuousOn`).  The remaining bookkeeping is
identical to `reduction.lean`: the general lemmas `Work.OddCurve.LowSlope.momentB_eq_centIntegral`
and `Work.OddCurve.LowSlope.inertiaIntegral_eq_shifted` (stated for an arbitrary profile) convert
the centroid and inertia conditions into the hypotheses of `cl1_free`. -/
theorem lowSlope_momentEqs_free (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hcent : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.LowSlope.centIntegral n (Work.OddVolterra.Free.envProfileFree h x y) x y s = 0)
    (hiner : ∀ s ∈ Set.Icc a b, (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
      Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y) x y s =
        Work.OddCurve.LowSlope.ballInertiaConst n)
    (hvalb : Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) b =
      ((2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballInertiaConst n) / Real.sqrt (1 + b ^ 2)) :
    (∀ s ∈ Set.Icc a b,
        Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
          ((2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballInertiaConst n) / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s ∈ Set.Icc a b,
        Work.OddCurve.momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0) := by
  refine ⟨?_, ?_⟩
  · refine cl1_free n hn H ha hab (fun s hs => ?_) (fun s hs => ?_) hvalb
    · rw [Work.OddCurve.LowSlope.momentB_eq_centIntegral (hzero s hs) (hder0 s hs)]
      exact hcent s hs
    · rw [Work.OddCurve.LowSlope.inertiaIntegral_eq_shifted (hzero s hs) (hder0 s hs)]
      exact hiner s hs
  · intro s hs
    rw [Work.OddCurve.LowSlope.momentB_eq_centIntegral (hzero s hs) (hder0 s hs)]
    exact hcent s hs

end

end Work.OddVolterra.Free
