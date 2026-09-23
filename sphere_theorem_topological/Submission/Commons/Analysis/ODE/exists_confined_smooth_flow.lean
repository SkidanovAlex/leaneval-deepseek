import Mathlib
import Submission.Commons.Analysis.ODE.uniform_flow_compact_of_contDiffOn
import Submission.Commons.Analysis.ODE.exists_confined_time_of_flow

namespace Commons.Analysis.ODE

/-- **Existence of a confined smooth local flow.**

Let `F : E → E` be `C^∞` on an open set `W` of a complete real normed space `E`, and let `K ⊆ W`
be compact.  Then there are `ρ > 0` and a family `α : E → ℝ → E` such that for every `p ∈ K`:
`α p 0 = p`, `t ↦ α p t` solves `x' = F x` on `[-ρ, ρ]`, the trajectory stays inside `W` on
`[-ρ, ρ]`, and the section `q ↦ α q t` is `C^∞` at `p` for every `|t| ≤ ρ`.

This combines the uniform local flow of a `C^∞` field on an open set
(`Commons.Analysis.ODE.uniform_flow_compact_of_contDiffOn`), which provides the solution family and
its smooth dependence on the initial point, with the uniform confinement lemma
(`Commons.Analysis.ODE.exists_confined_time_of_flow`), which shows that every solution starting in
the compact set `K` stays in `W` for a *uniformly* small time: shrinking the time only improves the
other properties. -/
theorem exists_confined_smooth_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ α : E → ℝ → E,
      (∀ p ∈ K, α p 0 = p) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (F (α p t)) t) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ → α p t ∈ W) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ →
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : E => α q t) p) := by
  obtain ⟨ρ₀, hρ₀, α, hα0, hαode, hαsm⟩ :=
    uniform_flow_compact_of_contDiffOn hW hFW hK hKW
  obtain ⟨ρ, hρ, hρle, hρW⟩ :=
    exists_confined_time_of_flow hW hFW.continuousOn hK hKW hρ₀ hα0 hαode
  exact ⟨ρ, hρ, α, hα0,
    fun p hp t ht => hαode p hp t (le_trans ht hρle),
    hρW,
    fun p hp t ht => hαsm p hp t (le_trans ht hρle)⟩

end Commons.Analysis.ODE
