import Mathlib
import Submission.Work.Analysis.IonescuWainger.FourierZ

namespace Work.KMTPlan.A6Clean

open MeasureTheory

/-- A function on the frequency circle `ℝ/ℤ` that is `L²` for the Haar (probability) measure,
restricted to a measurable subset of the fundamental domain `(-1/2, 1/2]` and then viewed as a
function of the real variable, is again `L²` for Lebesgue measure on `ℝ`.

The proof passes to the restricted measure: the indicator is `L²` for `volume` iff the function is
`L²` for `volume.restrict S`; the covering map `ℝ → ℝ/ℤ` is measure preserving from
`volume.restrict (Ioc (-1/2) (1/2))` to the circle, so `F` composed with it is `L²` on that
interval; and `volume.restrict S ≤ volume.restrict (Ioc (-1/2) (1/2))` since `S` sits inside it. -/
theorem liftMemLpTwo {F : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hF : MeasureTheory.MemLp F 2 Work.Analysis.IonescuWainger.circleMeasure)
    {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Set.Ioc (-(1 / 2)) (1 / 2)) :
    MeasureTheory.MemLp (S.indicator (fun ξ : ℝ => F ((ξ : ℝ) : Work.Analysis.IonescuWainger.Circle)))
      2 MeasureTheory.volume := by
  rw [MeasureTheory.memLp_indicator_iff_restrict hS]
  have hsub' : S ⊆ Set.Ioc (-(1 / 2)) (-(1 / 2) + 1) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hsub hx
    exact ⟨h1, by linarith⟩
  have hle : volume.restrict S ≤ volume.restrict (Set.Ioc (-(1 / 2)) (-(1 / 2) + 1)) :=
    Measure.restrict_mono hsub' le_rfl
  have hF' : MeasureTheory.MemLp F 2 (volume : Measure Work.Analysis.IonescuWainger.Circle) :=
    hF.of_haarAddCircle
  have hcomp := hF'.comp_measurePreserving (AddCircle.measurePreserving_mk (T := 1) (-(1 / 2)))
  exact hcomp.mono_measure hle

end Work.KMTPlan.A6Clean
