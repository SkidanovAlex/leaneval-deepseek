import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

set_option linter.unusedVariables false

open Filter Topology Set

/-- The closed pieces `{x | |x - x₀| ≤ ρ ∧ ∀ k ≥ n, ‖f k x‖ ≤ w k * exp (-(s k * ε))}` of the
"good set" of the real-line Cartan lemma are closed.  On the compact interval `|x - x₀| ≤ ρ`
every `f k` is continuous (it is holomorphic on the open set `U` containing that interval), so the
condition `‖f k x‖ ≤ w k * exp (-(s k * ε))` is preserved under limits. -/
theorem rcBclosed {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → ℂ}
    (hf : ∀ k, DifferentiableOn ℂ (f k) U) {w s : ℕ → ℝ} {x₀ ρ ε : ℝ} (hρ : 0 < ρ) {n : ℕ}
    (hsub : ∀ x : ℝ, |x - x₀| ≤ ρ → (x : ℂ) ∈ U) :
    IsClosed {x : ℝ | |x - x₀| ≤ ρ ∧ ∀ k ≥ n, ‖f k x‖ ≤ w k * Real.exp (-(s k * ε))} := by
  apply IsSeqClosed.isClosed
  intro u x hu hx
  have hxρ : |x - x₀| ≤ ρ := by
    have h1 : Tendsto (fun m : ℕ => |u m - x₀|) atTop (𝓝 |x - x₀|) :=
      (hx.sub tendsto_const_nhds).abs
    exact le_of_tendsto' h1 (fun m => (hu m).1)
  have hxc : (x : ℂ) ∈ U := hsub x hxρ
  refine ⟨hxρ, ?_⟩
  intro k hk
  have hkcont : ContinuousAt (f k) (x : ℂ) :=
    (hf k).continuousOn.continuousAt (hU.mem_nhds hxc)
  have htu : Tendsto (fun m : ℕ => (u m : ℂ)) atTop (𝓝 (x : ℂ)) :=
    (Complex.continuous_ofReal.tendsto x).comp hx
  have hn : Tendsto (fun m : ℕ => ‖f k (u m : ℂ)‖) atTop (𝓝 ‖f k (x : ℂ)‖) :=
    (hkcont.tendsto.comp htu).norm
  exact le_of_tendsto' hn (fun m => (hu m).2 k hk)

end Work.TMComp.RealCartan
