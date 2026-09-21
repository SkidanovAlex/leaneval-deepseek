import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.rad_nonpos_outside

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

/-- **Passing from the moving section to a fixed interval.**  If `f` vanishes below `c`
and above `d`, and `a ≤ c ≤ d ≤ b`, then the integral of `f` over `[a,b]` is the integral of `f`
over `[c,d]`.

The proof is the indicator argument: on `Ioc a b` the function `f` agrees with the indicator of
`Ioc c d`, so the integral over `Ioc a b` equals the integral of the indicator, which is the
integral over `Ioc a b ∩ Ioc c d = Ioc c d`.  No integrability or measurability of `f` is needed. -/
lemma intervalIntegral_eq_of_eq_zero_outside {f : ℝ → ℝ} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hleft : ∀ t, t ≤ c → f t = 0) (hright : ∀ t, d ≤ t → f t = 0) :
    ∫ t in a..b, f t = ∫ t in c..d, f t := by
  have hab : a ≤ b := le_trans hac (le_trans hcd hdb)
  have hpoint : ∀ x, x ∈ Set.Ioc a b → f x = (Set.Ioc c d).indicator f x := by
    intro x _
    by_cases hxc : x ≤ c
    · rw [hleft x hxc]
      exact (Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hxc)) f).symm
    · push Not at hxc
      by_cases hxd : x ≤ d
      · exact (Set.indicator_of_mem (s := Set.Ioc c d)
          (show x ∈ Set.Ioc c d from ⟨hxc, hxd⟩) f).symm
      · push Not at hxd
        rw [hright x hxd.le]
        exact (Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hxd)) f).symm
  have hsubset : Set.Ioc c d ⊆ Set.Ioc a b :=
    fun x hx => ⟨lt_of_le_of_lt hac hx.1, le_trans hx.2 hdb⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsubset]

/-- **The moment integrals only see the cut section.**  For an envelope curve `H` and a slope
`s > 0`, the radicand `rad h f s` is non-positive outside the section `(-(x s), y s)`
(`Work.OddCurve.rad_nonpos_outside`), so `Real.sqrt` of it vanishes there and both integrands of
`momentA` and `momentB` are identically zero outside the section.  Hence, for any interval
`[a,b]` containing the section, the two moment integrals may be computed over `[a,b]` instead of
over the section. -/
theorem moment_eqs_eq_integral_Icc (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {s a b : ℝ} (hs : 0 < s)
    (ha : a ≤ -(x s)) (hb : y s ≤ b) :
    Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      (∫ t in a..b, Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ n *
        Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) ∧
    Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      (∫ t in a..b, Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t) *
        (t + deriv h s)) := by
  set f := Work.OddEnvelope.envelopeProfile h x y with hf
  have hx : 0 < x s := (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_x H).pos hs
  have hy : 0 < y s := (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_y H).pos hs
  have hcd : -(x s) ≤ y s := by linarith
  have hle : ∀ t, t ≤ -(x s) ∨ y s ≤ t → rad h f s t ≤ 0 := by
    intro t ht
    rw [hf]
    exact rad_nonpos_outside (x := x) (y := y) H hs ht
  have hleftA : ∀ t, t ≤ -(x s) → rad h f s t ^ n * Real.sqrt (rad h f s t) = 0 := by
    intro t ht
    rw [Real.sqrt_eq_zero_of_nonpos (hle t (Or.inl ht)), mul_zero]
  have hrightA : ∀ t, y s ≤ t → rad h f s t ^ n * Real.sqrt (rad h f s t) = 0 := by
    intro t ht
    rw [Real.sqrt_eq_zero_of_nonpos (hle t (Or.inr ht)), mul_zero]
  have hleftB : ∀ t, t ≤ -(x s) →
      rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) * (t + deriv h s) = 0 := by
    intro t ht
    simp [Real.sqrt_eq_zero_of_nonpos (hle t (Or.inl ht))]
  have hrightB : ∀ t, y s ≤ t →
      rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) * (t + deriv h s) = 0 := by
    intro t ht
    simp [Real.sqrt_eq_zero_of_nonpos (hle t (Or.inr ht))]
  have hA := intervalIntegral_eq_of_eq_zero_outside (f := fun t =>
      rad h f s t ^ n * Real.sqrt (rad h f s t)) ha hcd hb hleftA hrightA
  have hB := intervalIntegral_eq_of_eq_zero_outside (f := fun t =>
      rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) * (t + deriv h s))
    ha hcd hb hleftB hrightB
  constructor
  · rw [momentA_def]
    exact hA.symm
  · rw [momentB_def]
    exact hB.symm

end

end Work.OddCurve
