import Mathlib
import Submission.Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero
import Submission.Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall

open Complex Metric

namespace Commons.Analysis.Complex

/-- If `f` is real differentiable on an open set `V` and all Wirtinger `∂̄`-derivatives vanish
on `V`, then `f` is complex differentiable on `V`. -/
theorem differentiableOn_complex_of_dbar_eq_zero {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hf : DifferentiableOn ℝ f V)
    (h : ∀ (j : Fin d) (z : Fin d → ℂ), z ∈ V →
      fderiv ℝ f z (Pi.single j (1 : ℂ)) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I) = 0) :
    DifferentiableOn ℂ f V := by
  intro z hz
  have hz' : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (hV.mem_nhds hz)
  rw [show DifferentiableWithinAt ℂ f V z ↔ DifferentiableAt ℂ f z from
    ⟨fun h => h.differentiableAt (hV.mem_nhds hz), fun h => h.differentiableWithinAt⟩]
  rw [differentiableAt_iff_restrictScalars ℝ hz']
  obtain ⟨g', hg'⟩ :=
    exists_complexLinear_of_map_smul_I (fderiv ℝ f z) (map_smul_I_of_basis (fun j => h j z hz))
  exact ⟨g', hg'⟩

/-- If `f : (Fin d → ℂ) → ℂ` is real-differentiable on an open set `V` and its Wirtinger
`∂̄`-derivatives vanish on `V`, then `f` is complex analytic on `V`. -/
theorem analyticOnNhd_of_dbar_eq_zero {d : ℕ} {f : (Fin d → ℂ) → ℂ} {V : Set (Fin d → ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℝ f V)
    (h : ∀ (j : Fin d) (z : Fin d → ℂ), z ∈ V →
      fderiv ℝ f z (Pi.single j (1 : ℂ)) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I) = 0) :
    AnalyticOnNhd ℂ f V := by
  have hdiff : DifferentiableOn ℂ f V := differentiableOn_complex_of_dbar_eq_zero hV hf h
  intro z hz
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hz)
  refine analyticAt_of_differentiableOn_closedBall (R := ε / 2) (by positivity) ?_
  refine hdiff.mono (fun y hy => hεV ?_)
  rw [mem_ball]
  have hy' : dist y z ≤ ε / 2 := mem_closedBall.mp hy
  linarith

end Commons.Analysis.Complex
