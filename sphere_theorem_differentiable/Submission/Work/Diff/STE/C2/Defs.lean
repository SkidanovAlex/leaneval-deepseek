/-
# Layer C2 (DeTurck pull-back): the packaged constructions

This file packages the raw definitions of `Defs0.lean` into the objects used by the statement of
`Work.Diff.STE.C2.ricci_of_deTurck`:

* `pullCov φ cov` — the pull-back of a covariant derivative along a diffeomorphism `φ`, as a
  bundled `CovariantDerivative` (the covariant-derivative axioms are proved in the child module
  `Submission.Work.Diff.STE.C2.pullCov_isCovariantDerivative`);
* `pullSMet φ g` — the pull-back of a smooth Riemannian metric, as an `SMet` (the smoothness of the
  section is the frame-matrix computation of the child module
  `Submission.Work.Diff.STE.C2.pullMetBilin_frameMat_contMDiffAt`).

Both are the ingredients of the classical DeTurck argument: if `φ_t` is the flow of a field `Y`
and `ĝ` solves `∂ₜĝ = -2 Ric(ĝ) + L_Y ĝ`, then `φ_t^* ĝ_t` solves the Ricci flow equation.
-/

import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.STE.C2.Defs0
import Submission.Work.Diff.STE.C2.pullCov_isCovariantDerivative
import Submission.Work.Diff.STE.C2.pullMetBilin_frameMat_contMDiffAt
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.STE.Man.exists_sMet_of_chartData

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

/-! ## The pull-back of a connection -/

/-- **The pull-back of a covariant derivative along a diffeomorphism.** -/
noncomputable def pullCov (φ : M ≃ₘ⟮I, I⟯ M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    CovariantDerivative I E (TangentSpace I (M := M)) where
  toFun := pullCovFun φ cov
  isCovariantDerivativeOnUniv := pullCov_isCovariantDerivative φ cov

@[simp] theorem pullCov_apply (φ : M ≃ₘ⟮I, I⟯ M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    pullCov φ cov σ x v = pullCovFun φ cov σ x v := rfl

/-! ## The pull-back of a metric -/

/-- **The pull-back of a smooth Riemannian metric along a diffeomorphism.** -/
noncomputable def pullSMet (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M) : SMet I M where
  inner := pullMetBilin φ g
  symm := pullMetBilin_symm φ g
  pos := pullMetBilin_pos φ g
  isVonNBounded := fun x ↦
    Work.Diff.STE.Man.isVonNBounded_of_posDef (I := I)
      (pullMetBilin φ g) (pullMetBilin_pos φ g) x
  contMDiff := fun x₀ ↦
    Work.Diff.STE.Man.section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀)
      (γ := pullMetBilin φ g) (pullMetBilin_frameMat_contMDiffAt φ g x₀)

@[simp] theorem pullSMet_inner (φ : M ≃ₘ⟮I, I⟯ M) (g : SMet I M)
    (x : M) (u v : TangentSpace I x) :
    (pullSMet φ g).inner x u v = pullMetBilin φ g x u v := rfl

end Work.Diff.STE.C2
