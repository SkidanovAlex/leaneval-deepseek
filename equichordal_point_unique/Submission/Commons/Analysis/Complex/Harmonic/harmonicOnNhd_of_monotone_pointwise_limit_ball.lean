import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Harnack's convergence principle for an arbitrary ball.**  Let `v n` be harmonic on the open
ball `Metric.ball a R`, pointwise increasing on that ball, with pointwise limit `u` (finite-valued
on the whole ball).  Then `u` is harmonic on `Metric.ball a R`.  This is the general-centre
version of `harmonicOnNhd_of_monotone_pointwise_limit`, obtained by translating to the ball
centred at the origin. -/
theorem harmonicOnNhd_of_monotone_pointwise_limit_ball {v : ℕ → ℂ → ℝ} {u : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hv : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (v n) (Metric.ball a R))
    (hmono : ∀ n : ℕ, ∀ z : ℂ, z ∈ Metric.ball a R → v n z ≤ v (n + 1) z)
    (hlim : ∀ z : ℂ, z ∈ Metric.ball a R →
      Filter.Tendsto (fun n : ℕ => v n z) Filter.atTop (nhds (u z))) :
    InnerProductSpace.HarmonicOnNhd u (Metric.ball a R) := by
  let W : ℕ → ℂ → ℝ := fun n z => v n (a + z)
  let U : ℂ → ℝ := fun z => u (a + z)
  -- membership transfer `ball 0 R → ball a R` for the translated argument
  have hmem : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) R → a + z ∈ Metric.ball a R := by
    intro z hz
    have hzR : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
    simpa [mem_ball, dist_eq_norm, add_sub_cancel_left] using hzR
  -- translated harmonicity
  have hW_harm : ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (W n) (Metric.ball (0 : ℂ) R) := by
    intro n z hz
    have hz' : a + z ∈ Metric.ball a R := hmem z hz
    have hcomp : InnerProductSpace.HarmonicAt (fun ζ : ℂ => v n (a + ζ)) z :=
      Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
        (f := fun ζ : ℂ => a + ζ) (x := z) (by fun_prop) (hv n (a + z) hz')
    simpa [W] using hcomp
  -- translated monotonicity
  have hW_mono : ∀ n : ℕ, ∀ z : ℂ, ‖z‖ < R → W n z ≤ W (n + 1) z := by
    intro n z hz
    have hz' : a + z ∈ Metric.ball a R :=
      hmem z (by simpa [mem_ball, dist_eq_norm] using hz)
    simpa [W] using hmono n (a + z) hz'
  -- translated pointwise convergence
  have hW_lim : ∀ z : ℂ, ‖z‖ < R →
      Filter.Tendsto (fun n : ℕ => W n z) Filter.atTop (nhds (U z)) := by
    intro z hz
    have hz' : a + z ∈ Metric.ball a R :=
      hmem z (by simpa [mem_ball, dist_eq_norm] using hz)
    simpa [W, U] using hlim (a + z) hz'
  -- apply the origin-centred Harnack convergence principle to the translate
  have hU_harm : InnerProductSpace.HarmonicOnNhd U (Metric.ball (0 : ℂ) R) :=
    harmonicOnNhd_of_monotone_pointwise_limit (v := W) (u := U) (R := R)
      hW_harm hW_mono hW_lim
  -- translate harmonicity back
  intro y hy
  have hyR : ‖y - a‖ < R := by
    have h := hy
    rw [mem_ball, dist_eq_norm] at h
    simpa using h
  have hzmem : y - a ∈ Metric.ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hyR
  have hUy : InnerProductSpace.HarmonicAt U (y - a) := hU_harm (y - a) hzmem
  have hcomp : InnerProductSpace.HarmonicAt (fun w : ℂ => U (w - a)) y :=
    Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (f := fun w : ℂ => w - a) (x := y) (by fun_prop) hUy
  have heq : (fun w : ℂ => U (w - a)) = u := by
    funext w
    simp only [U]
    congr 1
    ring
  rwa [heq] at hcomp

end Commons.Analysis.Complex.Harmonic
