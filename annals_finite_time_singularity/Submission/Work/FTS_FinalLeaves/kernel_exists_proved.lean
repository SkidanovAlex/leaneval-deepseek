/-
Copyright: work module for the Elgindi finite-time singularity project.

# Existence of a smooth mollifier kernel

`Work.FTS.StrongEps.IsSmoothKernel ρ` requires `ρ` to be `C^∞`, continuous, supported in the
*closed Euclidean unit ball* of `ℝ²`, nonnegative with total mass `1`.

Such a `ρ` is obtained from an arbitrary smooth bump function by normalising it by its integral.
Mathlib supplies everything needed:

* `ContDiffBump.normed μ` (in `Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`) is the
  normalisation `x ↦ f x / ∫ y, f y ∂μ` of a `ContDiffBump f`, with
  * `integral_normed : ∫ x, f.normed μ x ∂μ = 1`,
  * `support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut`,
  * `contDiff_normed`, `continuous_normed`, `nonneg_normed`.

The one point to check is the geometric one: the ambient norm on `ℝ × ℝ` is the *max* norm
(`Prod.norm_def`), so the support of the bump, a max-norm ball of radius `rOut`, is contained in
the Euclidean ball of radius `√2 · rOut`.  Taking `rOut = 1/2` therefore puts the support inside
the closed Euclidean unit ball.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open MeasureTheory Set Filter

noncomputable section

/-- The smooth bump, centred at the origin of `ℝ²`, with inner radius `1/4` and outer radius
`1/2`.  The outer radius is chosen so that its support — the max-norm ball of radius `1/2` — lies
inside the closed *Euclidean* unit ball. -/
def kerBump : ContDiffBump (0 : ℝ × ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The support condition of `IsMollKernel`, for the normalised bump: where the normalised bump
does not vanish, the Euclidean norm of the point is at most `1`. -/
theorem kerBump_support_pointwise (p : ℝ × ℝ)
    (hp : kerBump.normed volume p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
  have hp' : p ∈ Function.support (kerBump.normed volume) := hp
  rw [kerBump.support_normed_eq (μ := volume), Metric.mem_ball, dist_eq_norm, sub_zero,
    Prod.norm_def] at hp'
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hp'
  have hR : kerBump.rOut = 1 / 2 := rfl
  rw [hR] at h1 h2
  have h1' : |p.1| < 1 / 2 := by simpa only [Real.norm_eq_abs] using h1
  have h2' : |p.2| < 1 / 2 := by simpa only [Real.norm_eq_abs] using h2
  have e1 : p.1 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]; exact h1'
  have e2 : p.2 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]; exact h2'
  nlinarith

/-- **A smooth mollifier kernel exists**: the normalised bump function `kerBump.normed volume` is
`C^∞`, continuous, nonnegative, supported in the closed Euclidean unit ball and has total mass
`1`. -/
theorem kernel_exists_proved : ∃ ρ : ℝ × ℝ → ℝ, Work.FTS.StrongEps.IsSmoothKernel ρ := by
  refine ⟨kerBump.normed volume, fun n => kerBump.contDiff_normed (μ := volume), ?_⟩
  refine ⟨kerBump.continuous_normed, ?_, ?_, ?_⟩
  · intro p hp
    exact kerBump_support_pointwise p hp
  · exact fun p => kerBump.nonneg_normed p
  · simpa using kerBump.integral_normed (μ := volume)

end

end Work.FTS_FinalLeaves
