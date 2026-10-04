import Mathlib
import Submission.Diff.Interfaces
import Submission.Diff.Alg
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Uhlenbeck frame at a point: vocabulary and the normed-ring structure on matrices

The target lemma `Work.Diff.GE.uhlenbeck_frame_exists` constructs, at a fixed point `x` of a
manifold carrying a Ricci flow `G` on `[0,T)`, a family of `G s`-orthonormal frames at `x` moving
by the Uhlenbeck/Ricci rule `∂ₛ eᵢ = Ric(eᵢ)^♯`.

The proof reduces the problem at `x` to linear algebra: the metric at `x` is encoded in the matrix
`metricMat G x u s` of its inner products in a fixed `G t`-orthonormal frame `u`, and the required
frame is obtained from a (matrix) square root of the inverse of that matrix, normalised so that the
derivative at `t` is the Ricci matrix `ricMat`.

This module fixes that vocabulary and installs the *normed ring* structure on `(n × n)`-matrices
that the construction needs (the space of matrices with the operator-type norm is a complete normed
algebra, on which `Ring.inverse` is differentiable at the units — Mathlib's
`hasStrictFDerivAt_ringInverse`).  Mathlib deliberately does not register a matrix norm as a global
instance (several norms are natural), so the instances below are declared here, in a module that is
imported only by this development.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

/-! ## A normed-algebra structure on matrices -/

/-- The operator-type (`ℓ^∞`-operator) norm makes the `n × n` matrices over `ℝ` a normed ring.
Not registered by Mathlib (which offers several norms) — declared here for the Uhlenbeck frame
construction, where the matrix inverse and its derivative are needed. -/
noncomputable instance matrixInstNormedRing (n : ℕ) :
    NormedRing (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedRing

/-- The compatible `ℝ`-normed-algebra structure on matrices. -/
noncomputable instance matrixInstNormedAlgebra (n : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedAlgebra

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The metric matrix and the Ricci matrix at a point -/

/-- The matrix of inner products of the vectors `u i` at `x` for the metric `G s`. -/
noncomputable def metricMat (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (s : ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => (G s).inner x (u i) (u j)

/-- The matrix of the Ricci tensor of the metric `g` at `x` in the frame `u`. -/
noncomputable def ricMat (g : SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => ricAt (lcOf g) x (u i) (u j)

@[simp] lemma metricMat_apply (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (s : ℝ) (i j) :
    metricMat G x u s i j = (G s).inner x (u i) (u j) := rfl

@[simp] lemma ricMat_apply (g : SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (i j) :
    ricMat g x u i j = ricAt (lcOf g) x (u i) (u j) := rfl

/-- The metric matrix is symmetric. -/
lemma metricMat_symm (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (s : ℝ) :
    (metricMat G x u s).transpose = metricMat G x u s := by
  ext i j
  simp only [Matrix.transpose_apply, metricMat_apply]
  exact ((G s).symm x (u i) (u j)).symm

/-- In an orthonormal frame the metric matrix at that time is the identity. -/
lemma metricMat_eq_one (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (s : ℝ) (hu : IsONFrame (G s) x u) :
    metricMat G x u s = 1 := by
  ext i j
  rw [metricMat_apply, hu i j, Matrix.one_apply]

end Work.Diff.GE
