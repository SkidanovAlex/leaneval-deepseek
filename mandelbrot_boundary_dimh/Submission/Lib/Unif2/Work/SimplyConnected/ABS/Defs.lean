import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Defs
import Submission.Lib.Unif2.GreenData

/-!
# The Green function of a relatively compact domain, and its holomorphic modulus

This module fixes the two notions in which the disc lemma of Anghel–Bruin–Stan
(*Uniformization of Riemann surfaces revisited*, Theorem 10) is stated, in the *ambient* form
appropriate for the lemma `exists_biholomorphicOn_of_isSimplyConnected_open`.

All functions are functions on the ambient surface `X`; the domain of definition of the potential
theory is an open set `Ω ⊆ X`.

* `HasLogPoleOn Ω x₀ E` — the logarithmic pole of a potential at `x₀`, read inside `Ω`: in the
  preferred chart at `x₀` the quantity `E + log ‖ζ - ζ x₀‖` is bounded near `x₀` on `Ω`.

* `IsGreenOn Ω x₀ E` — `E` is the Green function of `Ω` with pole `x₀`: positive and harmonic off
  `x₀`, with a logarithmic pole at `x₀`, and with *relatively compact* superlevel sets inside `Ω`
  (this is the correct formalisation of "`E → 0` at the ideal boundary of `Ω`": the superlevel set
  `{ε ≤ E}` is a punctured neighbourhood of the pole, hence not closed).

* `IsModulusOn Ω x₀ E Φ` — `Φ` is a holomorphic modulus of `E` on `Ω`: `Φ` is holomorphic on `Ω`,
  has a simple zero at `x₀` (in the preferred chart) and modulus `exp (-E)` off `x₀`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The logarithmic pole of `E` at `x₀`, read inside `Ω`.**  In the preferred chart at `x₀`, the
quantity `E + log ‖ζ - ζ x₀‖` is bounded near `x₀` on `Ω`. -/
def HasLogPoleOn (Ω : Set X) (x₀ : X) (E : X → ℝ) : Prop :=
  ∃ C : ℝ, ∃ V : Set X, V ∈ 𝓝 x₀ ∧ ∀ x ∈ V, x ∈ Ω → x ≠ x₀ →
    |E x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖| ≤ C

/-- **The Green function of `Ω` with pole `x₀`.**  `E` is strictly positive at every point of `Ω`
other than `x₀`, harmonic on `Ω \ {x₀}`, has a logarithmic pole at `x₀`, and its superlevel sets are
*compactly contained in `Ω`*: for every `ε > 0` there is a compact `K ⊆ Ω` with `E < ε` on `Ω \ K`.
(This is the correct ambient form of "`E → 0` at the ideal boundary of `Ω`"; note that it is
*not* implied by `IsCompact (closure Ω)`, which only bounds the closures inside `X`.) -/
def IsGreenOn (Ω : Set X) (x₀ : X) (E : X → ℝ) : Prop :=
  (∀ x ∈ Ω, x ≠ x₀ → 0 < E x) ∧
  Submission.HarmonicOnX E (Ω \ {x₀}) ∧
  (∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ Ω, x ∉ K → E x < ε) ∧
  HasLogPoleOn Ω x₀ E

/-- **A holomorphic modulus of `E` on `Ω`.**  `Φ` is holomorphic on `Ω`, has a simple zero at `x₀`
in the preferred chart at `x₀`, and satisfies `‖Φ x‖ = exp (-E x)` for `x ∈ Ω`, `x ≠ x₀`. -/
def IsModulusOn (Ω : Set X) (x₀ : X) (E : X → ℝ) (Φ : X → ℂ) : Prop :=
  (∀ x ∈ Ω, Submission.HolomorphicOnXAt Φ x) ∧
  (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
    (Φ ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
      (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) ∧
  (∀ x ∈ Ω, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x)))

end Work.SimplyConnected.ABS
