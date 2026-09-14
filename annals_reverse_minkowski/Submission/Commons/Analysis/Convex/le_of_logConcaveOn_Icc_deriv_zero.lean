import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Convex

open Set

/-- **A log-concave function on `[0,1]` whose derivative vanishes at `0` is non-increasing.** 

Let `φ : ℝ → ℝ` be strictly positive on `[0,1]`, with `ψ = log ∘ φ` concave on `[0,1]`, and suppose
`φ` is differentiable at `0` with `φ'(0) = 0`. Then `φ 1 ≤ φ 0`.

Proof. By the chain rule `ψ'(0) = φ'(0)/φ(0) = 0`. The concave secant--derivative bound at the left
endpoint of the secant on `[0,1]` gives `slope ψ 0 1 ≤ ψ'(0) = 0`, i.e. `ψ 1 ≤ ψ 0`. Applying the
strict monotonicity of `log` on `(0, ∞)` (with `φ 1, φ 0 > 0`) yields `φ 1 ≤ φ 0`. -/
theorem le_of_logConcaveOn_Icc_deriv_zero {φ : ℝ → ℝ}
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < φ t)
    (hcave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => Real.log (φ t)))
    (hderiv : HasDerivAt φ 0 0) : φ 1 ≤ φ 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- Chain rule: `(log ∘ φ)'(0) = φ'(0) / φ 0 = 0`.
  have hdlog : HasDerivAt (fun s => Real.log (φ s)) 0 0 := by
    have h := hderiv.log (ne_of_gt (hpos 0 h0))
    simpa using h
  -- Concave secant bound at the left endpoint `0` of the secant on `[0,1]`.
  have hslope : slope (fun s => Real.log (φ s)) 0 1 ≤ 0 :=
    hcave.slope_le_of_hasDerivAt h0 h1 zero_lt_one hdlog
  simp only [slope_def_field, sub_zero, div_one] at hslope
  exact (Real.log_le_log_iff (hpos 1 h1) (hpos 0 h0)).mp (by linarith)

end Commons.Analysis.Convex