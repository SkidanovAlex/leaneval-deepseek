import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.hasDerivAt_momentA
import Submission.Work.OddEnvelope.Defs

/-!
# `cl1_forward` (Ryabogin's Lemma 4.2, forward direction) in the chord form of the odd case

The companion of `Work.OddCurve.LowSlope.cl1` (`cl1`, the *converse* direction).  Here the
moment equation `(A)` is *given* on the range `[a,b]` with the constant `K`, together with the
centroid condition `(B) = 0`; the conclusion is the **inertia condition** `(i1)`

`(1+s²)√(1+s²) ∫_{-x s}^{y s} (t + h'(s))² rad^{n-1/2} = K/(2n+1)`

on the *open* range `Ioo a b`.

The argument is the differentiation identity of the paper.  By
`Work.OddCurve.hasDerivAt_momentA`,

`(A)'(s) = -(2n+1) ∫ (s t + h s)(t + h'(s)) ψ^{n-1/2}`,   `ψ := rad h f s ·`,

while `(A)` being constantly `K/√(1+s²)` forces `(A)'(s) = -K s/(1+s²)^{3/2}`.  The pointwise
identity

`(s t + c)(t + d) = s (t + d)² + (c - s d)(t + d)`

splits the first integral into `s · (the inertia integral)` plus `(h s - s h'(s)) · (B)`; the
second term vanishes by the centroid condition, and dividing the resulting identity by the
positive slope `s` gives `(i1)` with the constant `K/(2n+1)`.

No smoothness of `h` beyond what `IsEnvelopeCurve` supplies is used, and no integration over a
range of slopes: the conclusion is pointwise on `Ioo a b`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **`cl1_forward`, chord form.**  If the moment equation `(A)` holds with constant `K` and the
centroid condition `(B)` vanishes on `Icc a b ⊆ (0,∞)`, then the inertia integral `(i1)` equals
`K/(2n+1)` there, normalised by `(1+s²)√(1+s²)`. -/
theorem cl1_forward (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        K / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) :
    ∀ s ∈ Set.Ioo a b,
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t))
      = K / (2 * (n : ℝ) + 1) := by
  intro s hs
  set F : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h x y with hF
  set J : ℝ := ∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t) with hJ
  have hs0 : 0 < s := lt_trans ha hs.1
  have hsIcc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hcont : Continuous F := Work.OddCurve.continuous_envelopeProfile H
  -- continuity of the radicand and of its half-integer powers, at fixed `s`
  have hrad_cont : Continuous (fun t : ℝ => Work.OddCurve.rad h F s t) := by
    have h2 : Continuous (fun t : ℝ => F t ^ 2) := hcont.pow 2
    have h1 : Continuous (fun t : ℝ => (s * t + h s) ^ 2) :=
      ((continuous_const.mul continuous_id).add continuous_const).pow 2
    have : Continuous (fun t : ℝ => F t ^ 2 - (s * t + h s) ^ 2) := h2.sub h1
    simpa only [Work.OddCurve.rad] using this
  have hAc : Continuous (fun t : ℝ => Work.OddCurve.rad h F s t ^ (n - 1) *
      Real.sqrt (Work.OddCurve.rad h F s t)) :=
    (hrad_cont.pow (n - 1)).mul (Real.continuous_sqrt.comp hrad_cont)
  have hAc' : Continuous (fun t : ℝ => (t + deriv h s) ^ 2 *
      Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) :=
    (((continuous_id.add continuous_const).pow 2).mul (hrad_cont.pow (n - 1))).mul
      (Real.continuous_sqrt.comp hrad_cont)
  -- `(A)` agrees with `K/√(1+u²)` near `s`, so its derivative at `s` is the derivative of the latter
  have hev : (fun u : ℝ => Work.OddCurve.momentA n h x y F u) =ᶠ[𝓝 s]
      fun u => K / Real.sqrt (1 + u ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact hA u (Set.Ioo_subset_Icc_self hu)
  have hdM : HasDerivAt (fun u : ℝ => Work.OddCurve.momentA n h x y F u)
      (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) s :=
    Work.OddCurve.hasDerivAt_momentA (n := n) hn H hs0
  have hdK : HasDerivAt (fun u : ℝ => K / Real.sqrt (1 + u ^ 2))
      (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) s :=
    hdM.congr_of_eventuallyEq hev.symm
  have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
  have hcube : (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) = Real.sqrt (1 + s ^ 2) ^ 3 := by
    have h : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    calc (1 + s ^ 2) * Real.sqrt (1 + s ^ 2)
        = Real.sqrt (1 + s ^ 2) ^ 2 * Real.sqrt (1 + s ^ 2) := by rw [h]
      _ = Real.sqrt (1 + s ^ 2) ^ 3 := by ring
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
      rw [hcube]
      field_simp
      ring
    rw [hval_eq] at h4
    exact h4
  have hEq : (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
      = -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) := hdK.unique hN
  -- the algebraic split of the derivative integral
  have hf1 : IntervalIntegrable (fun t : ℝ => s * ((t + deriv h s) ^ 2 *
      Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))
      volume (-(x s)) (y s) :=
    (continuous_const.mul hAc').intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun t : ℝ => (h s - s * deriv h s) * ((t + deriv h s) *
      (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))))
      volume (-(x s)) (y s) :=
    (continuous_const.mul ((continuous_id.add continuous_const).mul hAc)).intervalIntegrable _ _
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
    ring
  -- the centroid condition kills the second term
  have hval2 : (∫ t in (-(x s))..(y s), (t + deriv h s) *
      (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))) = 0 := by
    have h1 := hB s hsIcc
    rw [Work.OddCurve.momentB] at h1
    rw [← h1]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hIval : (∫ t in (-(x s))..(y s), -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
      = -(2 * (n : ℝ) + 1) * s * J := by
    rw [hJ]
    have hstep : (fun t : ℝ => -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))
        = (fun t : ℝ => (-(2 * (n : ℝ) + 1)) * ((s * t + h s) * (t + deriv h s) *
          (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))) := by
      funext t; ring
    rw [hstep, intervalIntegral.integral_const_mul, hsplit, hval2, mul_zero, add_zero]
    ring
  -- the two expressions for the derivative of `(A)` at `s`
  have hA1 : -(2 * (n : ℝ) + 1) * s * J = -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) :=
    hIval.symm.trans hEq
  have hA2 : -((2 * (n : ℝ) + 1) * s * J) = -(K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) := by
    rw [show -((2 * (n : ℝ) + 1) * s * J) = -(2 * (n : ℝ) + 1) * s * J by ring]
    exact hA1
  have hPJ : (2 * (n : ℝ) + 1) * J = K / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) := by
    have hD : ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≠ 0 := by positivity
    have hsne : s ≠ 0 := ne_of_gt hs0
    have h2 : ((2 * (n : ℝ) + 1) * J) * s = (K / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) * s := by
      calc ((2 * (n : ℝ) + 1) * J) * s = (2 * (n : ℝ) + 1) * s * J := by ring
        _ = K * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) := neg_inj.mp hA2
        _ = (K / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2))) * s := by ring
    exact mul_right_cancel₀ hsne h2
  have hgoal : ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * J) * (2 * (n : ℝ) + 1) = K := by
    have hD : ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≠ 0 := by positivity
    have h3 : ((2 * (n : ℝ) + 1) * J) * ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) = K := by
      rw [hPJ, div_mul_cancel₀ K hD]
    linear_combination h3
  have hP : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hP]
  exact hgoal

end

end Work.OddCurve.LowSlope
