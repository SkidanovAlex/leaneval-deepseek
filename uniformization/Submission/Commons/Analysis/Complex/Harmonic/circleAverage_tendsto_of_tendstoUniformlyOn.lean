import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.CircleAverage

noncomputable section
open Set Metric Complex Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Circle averages pass through uniform limits on the circle.**  If a sequence of
functions continuous on the circle `sphere c r` converges uniformly there to `u`, then their
circle averages of radius `r` converge to the circle average of `u`.
Proof: rewrite `Real.circleAverage` via its definition as an interval average over
`θ ∈ 0..2π` of the reparametrisation `circleMap c r θ`; uniform convergence on the sphere
gives uniform convergence of the reparametrisations on `[0, 2π]`
(`TendstoUniformlyOn.tendsto_comp`), and then use Mathlib
`TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn` and rescale by `(2π)⁻¹`.
Note `ContinuousOn.circleAverage` gives the continuity hypotheses for the limit `u`. -/
theorem circleAverage_tendsto_of_tendstoUniformlyOn {v : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hv : ∀ n : ℕ, ContinuousOn (v n) (sphere c r))
    (h : TendstoUniformlyOn v u atTop (sphere c r)) :
    Tendsto (fun n : ℕ => Real.circleAverage (v n) c r) atTop (𝓝 (Real.circleAverage u c r)) := by
  -- `circleMap c r` maps every real `θ` (in particular those in `uIcc 0 (2 * π)`)
  -- into `sphere c r`, because `0 < r`.
  have hmap : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r :=
    fun θ => circleMap_mem_sphere c hr.le θ
  -- The reparametrisations `θ ↦ v n (circleMap c r θ)` are continuous on `uIcc 0 (2 * π)`.
  have hcont : ∀ n : ℕ,
      ContinuousOn (fun θ : ℝ => v n (circleMap c r θ)) (uIcc 0 (2 * π)) := by
    intro n
    refine ContinuousOn.comp' (hv n) ?_ ?_
    · fun_prop
    · intro θ _
      exact hmap θ
  -- ... uniformly so: uniform convergence on the sphere, precomposed with `circleMap c r`.
  have hunif : TendstoUniformlyOn (fun n θ => v n (circleMap c r θ))
      (fun θ => u (circleMap c r θ)) atTop (uIcc 0 (2 * π)) := by
    intro U hU
    filter_upwards [h U hU] with n hn
    intro θ hθ
    exact hn (circleMap c r θ) (hmap θ)
  -- Uniform convergence on the interval passes through the integral over `0..2 * π`.
  have hI : Tendsto (fun n : ℕ => ∫ θ in 0..2 * π, v n (circleMap c r θ)) atTop
      (𝓝 (∫ θ in 0..2 * π, u (circleMap c r θ))) := by
    simpa using (TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (l := atTop) (F := fun n θ => v n (circleMap c r θ))
      (f := fun θ => u (circleMap c r θ)) (a := 0) (b := 2 * π)
      (Filter.Eventually.of_forall hcont) hunif)
  -- Rescale by `(2 * π)⁻¹` and unfold the definition of `Real.circleAverage`.
  simpa [Real.circleAverage] using hI.const_smul ((2 * π)⁻¹)

end Commons.Analysis.Complex.Harmonic