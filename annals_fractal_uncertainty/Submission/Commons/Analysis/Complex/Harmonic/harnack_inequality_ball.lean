import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.harnack_inequality
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

noncomputable section

open Set Metric Complex InnerProductSpace
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Harnack's inequality on an arbitrary ball.**  If `f : ℂ → ℝ` is harmonic in a
neighbourhood of the closed ball `Metric.closedBall a R` and non-negative there, then for every
`w` in the open ball `Metric.ball a R`,
`((R - ‖w - a‖) / (R + ‖w - a‖)) * f a ≤ f w ≤ ((R + ‖w - a‖) / (R - ‖w - a‖)) * f a`.

This is the translation of the centred version `harnack_inequality` (proved from the Poisson
integral formula): apply it to `z ↦ f (a + z)`, which is harmonic on the centred ball
`closedBall 0 R` by `harmonicAt_comp_analytic` (the map `z ↦ a + z` is complex-analytic). -/
theorem harnack_inequality_ball {a : ℂ} {R : ℝ} {f : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall a R))
    (hpos : ∀ z : ℂ, z ∈ Metric.closedBall a R → 0 ≤ f z) {w : ℂ} (hw : w ∈ Metric.ball a R) :
    ((R - ‖w - a‖) / (R + ‖w - a‖)) * f a ≤ f w ∧
      f w ≤ ((R + ‖w - a‖) / (R - ‖w - a‖)) * f a := by
  have hwlt : ‖w - a‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  -- The translate `z ↦ f (a + z)` is harmonic on the centred closed ball.
  have hFharm : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => f (a + z))
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hz' : a + z ∈ Metric.closedBall a R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      simpa using hz
    have han : AnalyticAt ℂ (fun ζ : ℂ => a + ζ) z := by
      have h : (fun ζ : ℂ => a + ζ) = (fun _ : ℂ => a) + id := by ext; simp
      rw [h]
      exact (analyticAt_const (v := a) (x := z)).add analyticAt_id
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (u := f) (f := fun ζ : ℂ => a + ζ) (x := z) han (hf (a + z) hz')
  -- Non-negativity of the translate on the centred closed ball.
  have hposF : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ f (a + z) := by
    intro z hz
    have hz' : a + z ∈ Metric.closedBall a R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hz
    exact hpos (a + z) hz'
  have hmain := harnack_inequality (f := fun z : ℂ => f (a + z)) (R := R) hFharm hposF hwlt
  simpa using hmain

end Commons.Analysis.Complex.Harmonic
