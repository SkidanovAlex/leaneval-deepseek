import Mathlib
import Submission.Work.OddVolterra.Defs

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology Interval

/-- If `Z · i` agrees near `c` with `profileX 1 - ∫_u^1 Z σ j`, then its derivative at `c`
is `Z c j`.  This is the fundamental theorem of calculus: the derivative of
`u ↦ ∫ σ in u..1, Z σ j` at `c` is `-(Z c j)`, so the derivative of the right-hand side
is `Z c j`, and the eventual equality transfers it to `Z · i`. -/
theorem deriv_row_of_identity {Z : ℝ → Work.OddVolterra.St} {c : ℝ} {i j : Fin 4}
    (hid : ∀ᶠ u in 𝓝 c, Z u i = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ j)
    (hint : IntervalIntegrable (fun σ : ℝ => Z σ j) volume c 1)
    (hmeass : StronglyMeasurableAtFilter (fun σ : ℝ => Z σ j) (𝓝 c) volume)
    (hcont : ContinuousAt (fun σ : ℝ => Z σ j) c) :
    deriv (fun u : ℝ => Z u i) c = Z c j := by
  have hFTC : HasDerivAt (fun u : ℝ => ∫ σ in u..(1 : ℝ), Z σ j) (-(Z c j)) c :=
    intervalIntegral.integral_hasDerivAt_left hint hmeass hcont
  have hRHS : HasDerivAt
      (fun u : ℝ => Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ j) (Z c j) c := by
    have h := (hasDerivAt_const (x := c) (c := Commons.Geometry.Ulam.profileX 1)).sub hFTC
    have hfun : ((fun _ : ℝ => Commons.Geometry.Ulam.profileX 1) -
        (fun u : ℝ => ∫ σ in u..(1 : ℝ), Z σ j))
        = (fun u : ℝ => Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ j) := by
      funext u; simp
    rw [hfun] at h
    simpa using h
  have hEE : (fun u : ℝ => Z u i) =ᶠ[𝓝 c]
      (fun u : ℝ => Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ j) := hid
  exact (hRHS.congr_of_eventuallyEq hEE).deriv

end Work.OddVolterra.WinData
