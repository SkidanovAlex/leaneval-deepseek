import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.Evol.RicDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction map of the fixed-vector curvature evolution (`Work.Diff.GE.fixRmEvolution`)

Under a Ricci flow, the components of the curvature in a *frozen* orthonormal frame evolve by

  `∂ₜ Rm(U,V,W,X) = (ΔRm)(U,V,W,X) + F(Rm)(U,V,W,X)`

where `ΔRm = lapRmAt` is the rough Laplacian of the `(0,4)`-tensor (traced in a `G t`-orthonormal
frame) and `F` is the quadratic reaction map of this file,

  `rmReact R = Q R - Xact R`.

The two pieces are the Hamilton reaction term `Q` (`Submission.Diff.Alg`) and the Uhlenbeck
correction `Xact` (`Work.Diff.Evol.Calc`), the four Ricci-action terms produced by the fact that in
*fixed* vectors the frame motion and the derivative of the metric contribute
`∂ₜ ⟨eᵢ,a⟩ = -Ricᵢₚ ⟨eₚ,a⟩`.

Sanity check (round sphere, `Rm = K·Iso`, `Ric = (n-1)K δ`, `K = 1/(1-2(n-1)t)`):
`Q(K·Iso) = 2(n-1)K²·Iso` and `Xact(K·Iso) = 4(n-1)K²·Iso`, so `rmReact(K·Iso) = -2(n-1)K²·Iso`,
which is exactly `∂ₜ Rm = -2(n-1)K²·Iso` in fixed vectors (with `ΔRm = 0`).  Equivalently,
`rmReact R = ricact R - Qhat R` on algebraic curvature tensors (`Work.Diff.Evol.Qhat_identity`).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable {n : ℕ}

/-- The reaction map of the fixed-vector curvature evolution: `R ↦ Q R - Xact R`, the Hamilton
reaction minus the four Ricci-action (Uhlenbeck) terms. -/
noncomputable def rmReact (n : ℕ) :
    Submission.Diff.Alg.Curv4 n → Submission.Diff.Alg.Curv4 n :=
  fun R => Submission.Diff.Alg.Q R - Work.Diff.Evol.Xact R

@[simp] lemma rmReact_apply (R : Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    rmReact n R i j k l = Submission.Diff.Alg.Q R i j k l - Work.Diff.Evol.Xact R i j k l := rfl

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- Notation-free wrapper for delegated statements: `A` is a `C^∞` section of the tangent bundle. -/
abbrev SmoothFld (A : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% A)

/-- Notation-free wrapper for delegated statements: `u : M → ℝ` is `C^∞`. -/
abbrev SmoothFn (u : M → ℝ) : Prop := CMDiff ∞ u

end Work.Diff.GE
