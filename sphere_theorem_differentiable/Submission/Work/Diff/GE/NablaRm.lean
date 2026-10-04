import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.Api
import Submission.Work.Diff.GE.curvbasic

import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `(0,5)`-tensor `∇Rm` of a metric: well-definedness, multilinearity, frame independence

The frozen file `Submission/Diff/Grad.lean` defines the components

`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)`

of the covariant derivative of the curvature of `g`, computed with the `Classical.epsilon`-chosen
smooth extensions `smoothExt x ·` of the five vectors.  This file proves that this is a genuine
`C^∞(M)`-multilinear form on the five tangent vectors (so that in particular the value does not
depend on the chosen extensions), and deduces that the sum of squares `dRmNormSq g x` is the same
in every orthonormal frame — i.e. `dRmNormSq` computes `|∇Rm|²`.

The strategy is the standard one: the expression defining `covRm` is `C^∞`-linear in each of its
arguments as an operation on smooth fields, hence depends on the fields only through their values
at `x` (a field vanishing at `x` is a combination `∑ fᵢ Yᵢ` with `fᵢ x = 0`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Curvature Submission.CurvatureVec Submission.ChartCurv
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The instances used to invoke the tensor library for the metric `g`. -/
abbrev withMetricInst (g : SMet I M) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  True

section rmP

variable (g : SMet I M)

/-- `rmP` is additive in its first argument. -/
theorem rmP_add_fst (hLC : LCSmooth I M) (x : M) (a₁ a₂ b c d : TangentSpace I x) :
    rmP g x (a₁ + a₂) b c d = rmP g x a₁ b c d + rmP g x a₂ b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x (a₁ + a₂) b d)) c
      = (g.inner x (rmVec (lcOf g) x a₁ b d)) c + (g.inner x (rmVec (lcOf g) x a₂ b d)) c
  rw [rmVec_add_left (lcOf g) hc x a₁ a₂ b d]
  simp only [map_add, ContinuousLinearMap.add_apply]

/-- `rmP` is additive in its second argument. -/
theorem rmP_add_snd (hLC : LCSmooth I M) (x : M) (a b₁ b₂ c d : TangentSpace I x) :
    rmP g x a (b₁ + b₂) c d = rmP g x a b₁ c d + rmP g x a b₂ c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x a (b₁ + b₂) d)) c
      = (g.inner x (rmVec (lcOf g) x a b₁ d)) c + (g.inner x (rmVec (lcOf g) x a b₂ d)) c
  rw [rmVec_add_middle (lcOf g) hc x a b₁ b₂ d]
  simp only [map_add, ContinuousLinearMap.add_apply]

/-- `rmP` is additive in its third argument. -/
theorem rmP_add_thd (hLC : LCSmooth I M) (x : M) (a b c₁ c₂ d : TangentSpace I x) :
    rmP g x a b (c₁ + c₂) d = rmP g x a b c₁ d + rmP g x a b c₂ d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact map_add (g.inner x (rmVec (lcOf g) x a b d)) c₁ c₂

/-- `rmP` is additive in its fourth argument. -/
theorem rmP_add_fth (hLC : LCSmooth I M) (x : M) (a b c d₁ d₂ : TangentSpace I x) :
    rmP g x a b c (d₁ + d₂) = rmP g x a b c d₁ + rmP g x a b c d₂ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x a b (d₁ + d₂))) c
      = (g.inner x (rmVec (lcOf g) x a b d₁)) c + (g.inner x (rmVec (lcOf g) x a b d₂)) c
  rw [rmVec_add_right (lcOf g) hc x a b d₁ d₂]
  simp only [map_add, ContinuousLinearMap.add_apply]

/-- `rmP` is homogeneous in its first argument. -/
theorem rmP_smul_fst (hLC : LCSmooth I M) (x : M) (r : ℝ) (a b c d : TangentSpace I x) :
    rmP g x (r • a) b c d = r * rmP g x a b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x (r • a) b d)) c
      = r * (g.inner x (rmVec (lcOf g) x a b d)) c
  rw [rmVec_smul_left (lcOf g) hc x r a b d]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `rmP` is homogeneous in its second argument. -/
theorem rmP_smul_snd (hLC : LCSmooth I M) (x : M) (r : ℝ) (a b c d : TangentSpace I x) :
    rmP g x a (r • b) c d = r * rmP g x a b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x a (r • b) d)) c
      = r * (g.inner x (rmVec (lcOf g) x a b d)) c
  rw [rmVec_smul_middle (lcOf g) hc x r a b d]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `rmP` is homogeneous in its third argument. -/
theorem rmP_smul_thd (hLC : LCSmooth I M) (x : M) (r : ℝ) (a b c d : TangentSpace I x) :
    rmP g x a b (r • c) d = r * rmP g x a b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  show (g.inner x (rmVec (lcOf g) x a b d)) (r • c)
      = r * (g.inner x (rmVec (lcOf g) x a b d)) c
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `rmP` is homogeneous in its fourth argument. -/
theorem rmP_smul_fth (hLC : LCSmooth I M) (x : M) (r : ℝ) (a b c d : TangentSpace I x) :
    rmP g x a b c (r • d) = r * rmP g x a b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hc : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  show (g.inner x (rmVec (lcOf g) x a b (r • d))) c
      = r * (g.inner x (rmVec (lcOf g) x a b d)) c
  rw [rmVec_smul_right (lcOf g) hc x r a b d]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

end rmP

/-! ## The second and third covariant derivatives of the curvature, and the rough Laplacians

These are the `(0,6)`- and `(0,7)`-tensors obtained by differentiating `∇Rm` once and twice more,
together with the traces that occur in Hamilton's evolution equations. -/

section Defs

/-- `(∇∇Rm)`: the defining expression, with arbitrary smooth fields in the slots
(the differentiation slot `u`, then the five slots of `∇Rm`). -/
noncomputable def cov2RmExt (g : SMet I M) (x : M) (u : TangentSpace I x)
    (V A B C D : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (fun y : M ↦ covRm g y (V y) (A y) (B y) (C y) (D y)) x u
    - covRm g x (lcOf g V x u) (A x) (B x) (C x) (D x)
    - covRm g x (V x) (lcOf g A x u) (B x) (C x) (D x)
    - covRm g x (V x) (A x) (lcOf g B x u) (C x) (D x)
    - covRm g x (V x) (A x) (B x) (lcOf g C x u) (D x)
    - covRm g x (V x) (A x) (B x) (C x) (lcOf g D x u)

/-- The `(0,6)`-tensor `∇∇Rm` at `x`. -/
noncomputable def cov2Rm (g : SMet I M) (x : M) (u v a b c d : TangentSpace I x) : ℝ :=
  cov2RmExt g x u (smoothExt x v) (smoothExt x a) (smoothExt x b) (smoothExt x c)
    (smoothExt x d)

/-- The `(0,7)`-tensor `∇∇∇Rm` at `x` (derivative of `∇∇Rm`). -/
noncomputable def cov3RmExt (g : SMet I M) (x : M) (w : TangentSpace I x)
    (U V A B C D : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (fun y : M ↦ cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w
    - cov2Rm g x (lcOf g U x w) (V x) (A x) (B x) (C x) (D x)
    - cov2Rm g x (U x) (lcOf g V x w) (A x) (B x) (C x) (D x)
    - cov2Rm g x (U x) (V x) (lcOf g A x w) (B x) (C x) (D x)
    - cov2Rm g x (U x) (V x) (A x) (lcOf g B x w) (C x) (D x)
    - cov2Rm g x (U x) (V x) (A x) (B x) (lcOf g C x w) (D x)
    - cov2Rm g x (U x) (V x) (A x) (B x) (C x) (lcOf g D x w)

/-- The `(0,7)`-tensor `∇∇∇Rm` at `x`. -/
noncomputable def cov3Rm (g : SMet I M) (x : M) (w u v a b c d : TangentSpace I x) : ℝ :=
  cov3RmExt g x w (smoothExt x u) (smoothExt x v) (smoothExt x a) (smoothExt x b)
    (smoothExt x c) (smoothExt x d)

/-- The rough Laplacian `ΔRm = ∑_m ∇_m∇_m Rm` of the curvature, contracted with four vectors. -/
noncomputable def lapRmAt (g : SMet I M) (x : M) (a b c d : TangentSpace I x) : ℝ :=
  ∑ m, cov2Rm g x (onFrame g x m) (onFrame g x m) a b c d

/-- The rough Laplacian `Δ(∇Rm) = ∑_m ∇_m∇_m ∇Rm` contracted with five vectors. -/
noncomputable def lapCovRmAt (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  ∑ m, cov3Rm g x (onFrame g x m) (onFrame g x m) v a b c d

/-- The quadratic reaction term `Q(Rm)` of Hamilton's equation, contracted with four vectors:
`∑ ⨯ Q(Rm)_{ijkl}` with the coefficients the coordinates in the chosen orthonormal frame. -/
noncomputable def qFormAt (g : SMet I M) (x : M) (a b c d : TangentSpace I x) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (onFrame g x i) a * g.inner x (onFrame g x j) b
      * g.inner x (onFrame g x k) c * g.inner x (onFrame g x l) d)
    * Q (rmC g x) i j k l

end Defs

end Work.Diff.GE
