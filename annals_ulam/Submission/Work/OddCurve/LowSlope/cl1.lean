import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.hasDerivAt_momentA

/-!
# `cl1` (Ryabogin's Lemma 4.2, converse direction) in the chord form of the odd case

On the low-slope range the bump vanishes (`h s = 0`, `h' s = 0`) and the cutting line is `s t`.
This file proves that on such a range, the *centroid* condition `(cmass)` together with the
*inertia* condition `(i1)` and the value of the *moment* equation `(A)` at a single slope force
`(A)` on the whole range, with the constant `(2n+1) c'` determined by the inertia constant.

The proof is the paper's: `d/ds (A) = -(2n+1) ∫ (s t + h s)(t + h'(s)) ψ^{n-1/2}`, the pointwise
identity `(s t + c)(t + d) = s (t + d)² + (c - s d)(t + d)` converts the right-hand side into
`-(2n+1) s ∫ (t + h')² ψ^{n-1/2}`, which `(i1)` evaluates as the derivative of
`(2n+1) c' / √(1+s²)`; hence `(A) - (2n+1)c'/√(1+s²)` is constant on the range, and its value at
the single slope `b` is `0`.

The derivative of the moment integral is `Work.OddCurve.hasDerivAt_momentA` (this chapter).
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

private lemma sqrt_cube (u : ℝ) :
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = Real.sqrt (1 + u ^ 2) ^ 3 := by
  have h : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  calc (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)
      = Real.sqrt (1 + u ^ 2) ^ 2 * Real.sqrt (1 + u ^ 2) := by rw [h]
    _ = Real.sqrt (1 + u ^ 2) ^ 3 := by ring

/-- **`cl1`, chord form.**  On a range `[a,b] ⊂ (0,∞)` on which the centroid condition `(cmass)`
holds (`momentB = 0`) and the inertia condition `(i1)` holds with constant `c'`, the moment
equation `(A)` — known at the single slope `b` with the constant `(2n+1) c'` — holds on the whole
range with that constant. -/
theorem cl1 (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {c' : ℝ}
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)
    (hI1 : ∀ s ∈ Set.Icc a b,
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) = c')
    (hval : Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) b =
      ((2 * (n : ℝ) + 1) * c') / Real.sqrt (1 + b ^ 2)) :
    ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        ((2 * (n : ℝ) + 1) * c') / Real.sqrt (1 + s ^ 2) := by
  set F : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h x y with hF
  set K : ℝ := (2 * (n : ℝ) + 1) * c' with hK
  have hcont : Continuous F := Work.OddCurve.continuous_envelopeProfile H
  -- The key step: `momentA - K/√(1+u²)` has vanishing derivative on the range.
  have key : ∀ s ∈ Set.Icc a b,
      HasDerivAt (fun u : ℝ => Work.OddCurve.momentA n h x y F u - K / Real.sqrt (1 + u ^ 2))
        0 s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hD : ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≠ 0 := by positivity
    have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
    -- continuity of the radicand and of its half-integer power, at fixed `s`
    have hrad_cont : Continuous (fun t : ℝ => Work.OddCurve.rad h F s t) := by
      have h2 : Continuous (fun t : ℝ => F t ^ 2) := hcont.pow 2
      have h1 : Continuous (fun t : ℝ => (s * t + h s) ^ 2) :=
        ((continuous_const.mul continuous_id).add continuous_const).pow 2
      have : Continuous (fun t : ℝ => F t ^ 2 - (s * t + h s) ^ 2) := h2.sub h1
      simpa only [Work.OddCurve.rad] using this
    have hAc : Continuous (fun t : ℝ =>
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) :=
      (hrad_cont.pow (n - 1)).mul (Real.continuous_sqrt.comp hrad_cont)
    have hAc' : Continuous (fun t : ℝ => (t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)) :=
      (((continuous_id.add continuous_const).pow 2).mul (hrad_cont.pow (n - 1))).mul
        (Real.continuous_sqrt.comp hrad_cont)
    -- the derivative of the moment integral, and integrability of the two pieces of the split
    have hA := Work.OddCurve.hasDerivAt_momentA (n := n) hn H (s := s) hs0
    have hf1 : IntervalIntegrable (fun t : ℝ => s * ((t + deriv h s) ^ 2 *
        Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t)))
        volume (-(x s)) (y s) :=
      (continuous_const.mul hAc').intervalIntegrable _ _
    have hf2 : IntervalIntegrable (fun t : ℝ => (h s - s * deriv h s) * ((t + deriv h s) *
        (Work.OddCurve.rad h F s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h F s t))))
        volume (-(x s)) (y s) :=
      (continuous_const.mul ((continuous_id.add continuous_const).mul hAc)).intervalIntegrable _ _
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

end

end Work.OddCurve.LowSlope
