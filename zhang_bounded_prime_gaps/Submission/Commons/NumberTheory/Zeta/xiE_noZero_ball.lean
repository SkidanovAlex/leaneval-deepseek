import Mathlib.NumberTheory.LSeries.RiemannZeta
import Submission.Commons.NumberTheory.Zeta.summable_totient_lcm_cpow

/-!
# A small ball around `0` free of zeros of the completed Riemann zeta `Ξ`

The entire completion

    Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)

(`Λ₀ = completedRiemannZeta₀` is the entire function `Λ(s) + 1/s − 1/(s−1)`)
satisfies `Ξ(0) = 1/2 ≠ 0`.  Since `Λ₀` is entire (`differentiable_completedZeta₀`),
`Ξ` is continuous at `0`, so the preimage of the punctured plane is a
neighbourhood of `0`, i.e. there is a radius `δ₀ > 0` (taken `≤ 1`) with
`Ξ(u) ≠ 0` for all `‖u‖ < δ₀`.

This fact is the "no zeros near the origin" input used when translating the
partial-fraction/Hadamard expansion of `Ξ` into bounds on `logDeriv Ξ`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Commons.NumberTheory.Zeta

/-- The entire completion `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)` has no zeros on a
small ball around `0` (indeed `Ξ(0) = 1/2 ≠ 0`). -/
theorem xiE_noZero_ball :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u : ℂ, ‖u‖ < δ₀ →
      ((1 / 2 : ℂ) + (1 / 2 : ℂ) * u * (u - 1) * completedRiemannZeta₀ u) ≠ 0 := by
  let F : ℂ → ℂ := fun u => (1 / 2 : ℂ) + (1 / 2 : ℂ) * u * (u - 1) * completedRiemannZeta₀ u
  have hF0 : F 0 ≠ 0 := by
    dsimp [F]
    norm_num
  have hcont : Continuous F := by
    dsimp [F]
    have hΛ : Continuous completedRiemannZeta₀ := differentiable_completedZeta₀.continuous
    fun_prop
  have hnhd : {u : ℂ | F u ≠ 0} ∈ 𝓝 (0 : ℂ) := by
    have hs : {z : ℂ | z ≠ 0} ∈ 𝓝 (F 0) := by
      exact isOpen_ne.mem_nhds hF0
    have hpre := hcont.continuousAt.preimage_mem_nhds hs
    simpa using hpre
  rcases (Metric.mem_nhds_iff.mp hnhd) with ⟨δ, hδpos, hball⟩
  refine ⟨min δ 1, ?_, ?_, ?_⟩
  · exact lt_min hδpos (by norm_num : (0 : ℝ) < 1)
  · exact min_le_right δ 1
  · intro u hu
    have huδ : u ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball]
      simpa using (lt_of_lt_of_le hu (min_le_left δ 1))
    exact hball huδ

end Commons.NumberTheory.Zeta