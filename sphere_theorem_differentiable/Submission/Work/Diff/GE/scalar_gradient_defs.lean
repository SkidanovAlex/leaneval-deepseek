import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the scalar-curvature gradient bound (`Work.Diff.GE.scalar_gradient_bound`)

`T : Fin n → Curv4 n` is the array of covariant derivatives `(∇_m Rm)_{ijkl}` of a curvature tensor
in an orthonormal frame.  This file fixes the two notions the algebraic bound is phrased with:

* `scTrace T m = ∑ᵢⱼ T m i j i j`, the scalar-curvature gradient `∇_m S`;
* `tfPart T m`, the trace-free part `T_m° = T_m − (scTrace T m / (n(n−1))) • Iso n` of the slice
  `T_m`, so that `frobSq (tfPart T m) = frobSq (T m) − 2 (scTrace T m)² / (n(n−1))`
  (`Work.Diff.GE.frobSq_eq_frobSq_tfPart`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- `∇_m S = ∑ᵢⱼ T m i j i j`: the scalar-curvature gradient encoded by a `(0,5)`-array. -/
noncomputable def scTrace {n : ℕ} (T : Fin n → Curv4 n) (m : Fin n) : ℝ :=
  ∑ i, ∑ j, T m i j i j

/-- The trace-free part of the `m`-th slice `T_m = ∇_m Rm` in an orthonormal frame:
`T_m° = T_m − (scTrace T m / (n(n−1))) • Iso n`. -/
noncomputable def tfPart {n : ℕ} (T : Fin n → Curv4 n) (m : Fin n) : Curv4 n :=
  fun a b c d => T m a b c d - (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n a b c d

/-- The squared norm of the trace-free part, summed over the derivative index: this is the
quantity `|∇Rm°|² = ∑_m (frobSq (T m) − 2 (scTrace T m)² / (n(n−1)))` of the statement. -/
noncomputable def tfNormSq {n : ℕ} (T : Fin n → Curv4 n) : ℝ :=
  ∑ m, frobSq (tfPart T m)

end Work.Diff.GE
