import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Chain.isCompact_Kset
import Submission.Work.Escape.exists_differentiableOn_ball_clog

/-!
# A ball around a point outside `Kset` carrying a branch of `πExp`

`Kset d hd` is the critical orbit of the pushed-down horn map `g`, together with `0`.  It is
compact (`Work.L61.isCompact_Kset`), hence closed, so every `x ∉ Kset` has a ball `ball x ε`
avoiding `Kset`.  Since `0 ∈ Kset`, that ball also avoids `0`, so the identity map is holomorphic
and nowhere vanishing there and admits a holomorphic logarithm `L₀` (`Escape`).  Then
`L z = L₀ z / (2πi)` is the required continuous branch of `πExp = exp(2πi ·)`:
`πExp (L z) = exp (2πi · L₀ z / (2πi)) = exp (L₀ z) = z`.
-/

open scoped Topology

namespace Work.L61.CovAux

/-- If `L₀` is a logarithm of the identity on a ball (`exp (L₀ z) = z`), then
`L₀ / (2πi)` is a branch of `πExp = exp (2πi ·)` there. -/
theorem piExp_div_two_pi_I {L₀ : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hL₀ : ∀ z ∈ Metric.ball c r, Complex.exp (L₀ z) = z) :
    ∀ z ∈ Metric.ball c r,
      MandelDim.piExp (L₀ z / (2 * (Real.pi : ℂ) * Complex.I)) = z := by
  intro z hz
  have h2pi : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  rw [MandelDim.piExp,
    show 2 * (Real.pi : ℂ) * Complex.I * (L₀ z / (2 * (Real.pi : ℂ) * Complex.I)) = L₀ z from
      mul_div_cancel₀ _ h2pi,
    hL₀ z hz]

/-- There is a ball around a point outside `Kset` which avoids `Kset` (and hence `0`), and on
which `πExp` admits a continuous branch. -/
theorem exists_ball_log_branch {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    (hd : MandelDim.HornData d) {x : ℂ} (hx : x ∈ (Work.L61.Kset d hd)ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ (Work.L61.Kset d hd)ᶜ ∧ (0 : ℂ) ∉ Metric.ball x ε ∧
      ∃ L : ℂ → ℂ, ContinuousOn L (Metric.ball x ε) ∧
        ∀ z ∈ Metric.ball x ε, MandelDim.piExp (L z) = z := by
  -- `Kset` is compact, hence closed, so its complement is a neighbourhood of `x`.
  have hclosed : IsClosed (Work.L61.Kset d hd) := (Work.L61.isCompact_Kset hd).isClosed
  have hopen : (Work.L61.Kset d hd)ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨ε, hε, hball, ?_, ?_⟩
  · -- `0 ∈ Kset`, so a ball avoiding `Kset` avoids `0`.
    intro hmem
    exact hball hmem (Work.L61.zero_mem_Kset d hd)
  · -- the identity is holomorphic and nowhere vanishing on the ball, hence has a logarithm
    have hne : ∀ z ∈ Metric.ball x ε, z ≠ 0 := by
      intro z hz hz0
      exact hball (hz0 ▸ hz) (Work.L61.zero_mem_Kset d hd)
    obtain ⟨L₀, hL₀diff, hL₀exp, _⟩ :=
      Work.Escape.exists_differentiableOn_ball_clog (g := fun z : ℂ => z)
        (c := x) (r := ε) differentiableOn_id hne
    exact ⟨fun z => L₀ z / (2 * (Real.pi : ℂ) * Complex.I),
      hL₀diff.continuousOn.div_const _, piExp_div_two_pi_I hL₀exp⟩

end Work.L61.CovAux
