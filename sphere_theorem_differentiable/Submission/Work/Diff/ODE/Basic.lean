/-
Definitions shared by the ODE area (`Submission/Work/Diff/ODE/flow_smooth.lean`).

The contract `Submission.Diff.SmoothFlow` asks for the jointly smooth global flow of a jointly
smooth *time-dependent* vector field `X` on a compact boundaryless manifold.  We phrase solutions
in "elapsed time": a solution started at absolute time `s` at the point `x` is a curve
`γ : ℝ → M` with `γ 0 = x` and `γ' τ = X (s + τ) (γ τ)`.
-/

import Mathlib
import Submission.Diff.ODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.ODE

open Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `IsXCurve X s x γ`: the curve `γ` (in elapsed time) is the solution of the time-dependent ODE
of `X` started at absolute time `s` at the point `x`, for all elapsed times. -/
def IsXCurve (X : ℝ → Π x : M, TangentSpace I x) (s : ℝ) (x : M) (γ : ℝ → M) : Prop :=
  γ 0 = x ∧ ∀ τ : ℝ,
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ τ ((1 : ℝ →L[ℝ] ℝ).smulRight (X (s + τ) (γ τ)))

/-- `IsXCurveOn X s x T γ`: the same as `IsXCurve`, but only required for the elapsed times
`|τ| < T`. -/
def IsXCurveOn (X : ℝ → Π x : M, TangentSpace I x) (s : ℝ) (x : M) (T : ℝ) (γ : ℝ → M) : Prop :=
  γ 0 = x ∧ ∀ τ : ℝ, |τ| < T →
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ τ ((1 : ℝ →L[ℝ] ℝ).smulRight (X (s + τ) (γ τ)))

lemma IsXCurve.isXCurveOn {X : ℝ → Π x : M, TangentSpace I x} {s : ℝ} {x : M} {γ : ℝ → M}
    (h : IsXCurve X s x γ) (T : ℝ) : IsXCurveOn X s x T γ :=
  ⟨h.1, fun τ _ => h.2 τ⟩

/-- **A local flow box** for the time-dependent field `X`.  `FL τ a y` is the position reached after
elapsed time `τ` when starting at absolute time `a` at the point `y`; this is claimed for all
`(a, y)` in the open set `U` and all `|τ| ≤ 2 * δ`.  Joint `C^∞`-smoothness in `(τ, a, y)` is
claimed at every `(a,y) ∈ U` and every `|τ| < 2 * δ`. -/
structure LocalBox (X : ℝ → Π x : M, TangentSpace I x) where
  δ : ℝ
  hδ : 0 < δ
  U : Set (ℝ × M)
  hU : IsOpen U
  FL : ℝ → ℝ → M → M
  hzero : ∀ a y, (a, y) ∈ U → FL 0 a y = y
  hode : ∀ a y, (a, y) ∈ U → ∀ τ : ℝ, |τ| ≤ 2 * δ →
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => FL σ a y) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + τ) (FL τ a y)))
  hsmooth : ∀ a y, (a, y) ∈ U → ∀ τ : ℝ, |τ| < 2 * δ →
    ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun r : (ℝ × ℝ) × M => FL r.1.1 r.1.2 r.2) ((τ, a), y)

end Work.Diff.ODE
