import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.GE.EvolB` : the fixed-vector `∇Rm` evolution (definitions)

This module is the entry point of the second, self-contained development of the fixed-vector
evolution estimate for `∇Rm` (`Work.Diff.GE.hasDerivWithinAt_covRm_le`).  The development lives
under `Submission/Work/Diff/GE/EvolB/` and only uses declarations of the rest of the workspace that
are *sorry-free* (checked with `#print axioms`).

**Level of differentiability.**  Everything here is stated for a *smooth* manifold,
`[IsManifold I ∞ M]` — the level at which the target statement
(`Work.Diff.GE.hasDerivWithinAt_covRm_frame_le`) lives.  (The definitions of
`Submission/Work/Diff/GE/covRmFixedEvolDefs.lean` are stated for an *analytic* manifold
`[IsManifold I ((⊤ : ENat) : WithTop ENat) M]`, which is why `EvolB` carries its own copies `rmP4B`,
`connVarB`, `covRmTimeDerivB` of `rmP4`, `connVar`, `covRmTimeDeriv`; those copies differ from the
originals only in that level.)

## Contents

* `lapRm4`, `react4`: `lapRmAt` / `reactionFormAt` as functions of a `4`-tuple of tangent vectors,
  so that the moving-slot product rule can be stated with `Function.update p j ·`.
* `rmP4B`: `rmP` on a `4`-tuple of tangent vectors.
* `connVarB`, `covRmTimeDerivB`: the connection-variation vector `s ↦ ∇^{G s}_v (smoothExt x a)` and
  the predicted time derivative of the fixed-vector component `s ↦ covRm (G s) x v a b c d`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `rmP` on a `4`-tuple of tangent vectors. -/
noncomputable def rmP4B (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) : ℝ :=
  rmP g x (p 0) (p 1) (p 2) (p 3)

/-- `lapRmAt` on a `4`-tuple of tangent vectors. -/
noncomputable def lapRm4 (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) : ℝ :=
  Work.Diff.GE.lapRmAt g x (p 0) (p 1) (p 2) (p 3)

/-- `reactionFormAt F` on a `4`-tuple of tangent vectors. -/
noncomputable def react4 (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) : ℝ :=
  Work.Diff.GE.reactionFormAt F g x (p 0) (p 1) (p 2) (p 3)

/-- `rmP4B` written out. -/
theorem rmP4B_apply (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) :
    rmP4B g x p = rmP g x (p 0) (p 1) (p 2) (p 3) := rfl

/-- `lapRm4` written out. -/
theorem lapRm4_apply (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) :
    lapRm4 g x p = Work.Diff.GE.lapRmAt g x (p 0) (p 1) (p 2) (p 3) := rfl

/-- `react4` written out. -/
theorem react4_apply (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) :
    react4 F g x p = Work.Diff.GE.reactionFormAt F g x (p 0) (p 1) (p 2) (p 3) := rfl

/-- The variation of the Levi-Civita connection in the direction `v`, as a function of time:
`s ↦ ∇^{G s}_{smoothExt x v} (smoothExt x a) (x)`. -/
noncomputable def connVarB (G : ℝ → SMet I M) (x : M) (a : TangentSpace I x)
    (v : TangentSpace I x) (s : ℝ) : TangentSpace I x :=
  lcOf (G s) (smoothExt x a) x v

/-- The predicted time derivative of the fixed-vector component `s ↦ covRm (G s) x v a b c d`
(see `Submission/Work/Diff/GE/covRmFixedEvolDefs.lean`); the only difference from
`Work.Diff.GE.covRmTimeDeriv` is the differentiability level of the manifold. -/
noncomputable def covRmTimeDerivB
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (G : ℝ → SMet I M) (t : ℝ) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  Work.Diff.GE.covLapRmAt (G t) x v a b c d
    + Work.Diff.GE.covReactionFormAt F (G t) x v a b c d
    - rmP (G t) x (deriv (connVarB G x a v) t) b c d
    - rmP (G t) x a (deriv (connVarB G x b v) t) c d
    - rmP (G t) x a b (deriv (connVarB G x c v) t) d
    - rmP (G t) x a b c (deriv (connVarB G x d v) t)

end Work.Diff.GE.EvolB
