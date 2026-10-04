import Mathlib
import Submission.Diff.Grad
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

/-!
# `Gest.Base`: the specification layer for the gradient estimate

`Submission/Diff/Grad.lean` (frozen) defines the pointwise quantities of Hamilton's gradient
estimate through `Classical.epsilon`-chosen objects: the smooth extension `smoothExt x u`, the
orthonormal frame `onFrame g x`, the pointwise curvature `rmVec`, the frame components
`rmFrame g x e`, and the scalar quantities `rmNormSq`, `dRmNormSq`, `scalAt`, `ricNormSq`,
`rmoNormSq`, `drmoNormSq`, `qPairAt`, `laplAt`, `gradSq`.

This module records the elementary *specifications* of those choices plus the plain algebraic
rewritings of the definitions that the proof of `Work.Diff.GE.gradient_estimate` needs.  It is the
import hub on which the auxiliary lemmas `Work.Diff.GE.Gest.*` (the Laplacian calculus and the

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
pure real-algebra lemmas) depend.
-/

namespace Work.Diff.GE.Gest

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## The chosen smooth extension -/

/-- The smooth extension chosen by `smoothExt` is smooth. -/
theorem smoothExt_contMDiff [T2Space M] (x : M) (u : TangentSpace I x) :
    CMDiff ∞ (T% (smoothExt x u)) :=
  (Classical.epsilon_spec
    (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u)).1

/-- The smooth extension chosen by `smoothExt` takes the prescribed value at `x`. -/
theorem smoothExt_apply_self [T2Space M] (x : M) (u : TangentSpace I x) :
    smoothExt x u x = u :=
  (Classical.epsilon_spec
    (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u)).2

/-! ## The chosen frame -/

/-- The chosen frame `onFrame g x` is `g`-orthonormal. -/
theorem isONFrame_onFrame (g : SMet I M) (x : M) : IsONFrame g x (onFrame g x) := by
  have hex : ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x, IsONFrame g x e := by
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    refine ⟨fun i => stdOrthonormalBasis ℝ (TangentSpace I x) i, ?_⟩
    intro i j
    rw [show g.inner x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
          (stdOrthonormalBasis ℝ (TangentSpace I x) j)
        = @inner ℝ _ _ (stdOrthonormalBasis ℝ (TangentSpace I x) i)
          (stdOrthonormalBasis ℝ (TangentSpace I x) j) from rfl]
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal i j]
    rfl
  exact Classical.epsilon_spec hex

/-! ## Definitional rewritings of the frozen definitions -/

/-- `|Rm°|² = |Rm|² − 2 scal²/(n(n−1))`, pointwise. -/
theorem rmoNormSq_eq (g : SMet I M) (x : M) :
    rmoNormSq g x
      = rmNormSq g x - 2 * scalAt g x ^ 2
          / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) := rfl

/-- `|∇Rm°|² = |∇Rm|² − 2|∇scal|²/(n(n−1))`, pointwise. -/
theorem drmoNormSq_eq (g : SMet I M) (x : M) :
    drmoNormSq g x
      = dRmNormSq g x - 2 * gradSq g (scalAt g) x
          / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) := rfl

/-! ## Nonnegativity of the squared norms -/

/-- `|Rm|² ≥ 0`. -/
theorem rmNormSq_nonneg (g : SMet I M) (x : M) : 0 ≤ rmNormSq g x := by
  rw [rmNormSq, frobSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _

/-- `|∇Rm|² ≥ 0`. -/
theorem dRmNormSq_nonneg (g : SMet I M) (x : M) : 0 ≤ dRmNormSq g x := by

  exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => sq_nonneg _

/-- `frobSq` is a sum of squares, hence nonnegative. -/
theorem frobSq_nonneg {n : ℕ} (R : Curv4 n) : 0 ≤ frobSq R := by
  rw [frobSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _

/-- `ricSq` is a sum of squares, hence nonnegative. -/
theorem ricSq_nonneg {n : ℕ} (R : Curv4 n) : 0 ≤ ricSq R := by
  rw [ricSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end Work.Diff.GE.Gest
