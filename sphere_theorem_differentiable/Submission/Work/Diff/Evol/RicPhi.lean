import Mathlib
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Frame
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci tensor as a function of fields, and its `Ext` patterns

The frozen modules define the covariant derivatives of the Ricci tensor pointwise, on the
`Classical.epsilon`-chosen extensions `smoothExt x ·` of the tangent vectors at `x`
(`Work.Diff.Evol.RicDeriv`: `covRic`, `cov2Ric`).  For the proof of the Ricci identity for `Ric`
(`Work.Diff.Evol.ricci_identity_ric`) they are used in the "field form": the same expressions
evaluated on arbitrary smooth fields.

* `ricF g A B` is the scalar function `y ↦ ricAt (lcOf g) y (A y) (B y)`;
* `dRicPhi g x v A B` is the `Ext` pattern of `ricF`: `∇_v Ric` evaluated on the slots `A B`
  (the derivative of `ricF g A B` along `v` minus the two connection corrections), so that
  `covRic g x v a b = dRicPhi g x v (smoothExt x a) (smoothExt x b)`;
* `cov2RicExt g x v U W A B` is the `Ext` pattern of `dRicPhi`: `∇_v∇_W Ric` evaluated on `A B`
  (the derivative of `dRicPhi g · (W ·) A B` along `v`, minus the three corrections that make it
  tensorial), so that
  `cov2Ric g x v w a b = cov2RicExt g x v (smoothExt x v) (smoothExt x w) (smoothExt x a)
  (smoothExt x b)`.

The `U`-field is kept as an explicit argument of `cov2RicExt` because the corrections involve the
derivative `∇_{U x} A`; in the applications `U x = v`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Notation-free wrapper for delegated statements: `A` is a `C^∞` section of the tangent bundle.
(`T%` and `∞` are scoped notations, so delegated statements, elaborated in files with plain
`import`s, use this wrapper instead.) -/
abbrev SmoothSec (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (A : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% A)

/-- Notation-free wrapper for delegated statements: `u` is a `C^∞` function. -/
abbrev SmoothFun (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (u : M → ℝ) : Prop := CMDiff ∞ u

/-- The Ricci tensor of `g` evaluated on two smooth fields, as a scalar function. -/
noncomputable def ricF (g : SMet I M) (A B : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  ricAt (lcOf g) y (A y) (B y)

/-- The `Ext` pattern of `ricF`: the covariant derivative `∇_v Ric` evaluated on the slots `A B`,
computed with the smooth fields `A B` and the direction `v`. -/
noncomputable def dRicPhi (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (ricF g A B) x v
    - ricAt (lcOf g) x (lcOf g A x v) (B x) - ricAt (lcOf g) x (A x) (lcOf g B x v)

/-- The `Ext` pattern of `dRicPhi`: the second covariant derivative `∇_v∇_W Ric` evaluated on the
slots `A B`.  The field `U` supplies the derivative `∇_{U x} A` of the slots along `v`. -/
noncomputable def cov2RicExt (g : SMet I M) (x : M) (v : TangentSpace I x)
    (U W A B : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (fun y : M ↦ dRicPhi g y (W y) A B) x v
    - dRicPhi g x (lcOf g W x v) A B
    - dRicPhi g x (W x) (fun y : M ↦ lcOf g A y (U y)) B
    - dRicPhi g x (W x) A (fun y : M ↦ lcOf g B y (U y))

/-- `covRic` is `dRicPhi` evaluated on the chosen extensions `smoothExt x ·`. -/
theorem covRic_eq_dRicPhi (g : SMet I M) (x : M) (v a b : TangentSpace I x) :
    covRic g x v a b = dRicPhi g x v (smoothExt x a) (smoothExt x b) := by
  have h : ricF g (smoothExt x a) (smoothExt x b)
      = fun y : M ↦ ricAt (lcOf g) y (smoothExt x a y) (smoothExt x b y) := rfl
  have ha : smoothExt x a x = a := Work.Diff.GE.smoothExt_apply x a
  have hb : smoothExt x b x = b := Work.Diff.GE.smoothExt_apply x b
  simp only [dRicPhi, h, covRic, ha, hb]

/-- The Leibniz identity, i.e. the definition of `dRicPhi` rearranged: the derivative of
`Ric(A,B)` along `v` is `(∇_v Ric)(A,B)` plus the two corrections `Ric(∇_v A, B)`, `Ric(A, ∇_v B)`. -/
theorem mvfderiv_ricF_eq (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B : Π y : M, TangentSpace I y) :
    mvfderiv I (ricF g A B) x v
      = dRicPhi g x v A B + ricAt (lcOf g) x (lcOf g A x v) (B x)
        + ricAt (lcOf g) x (A x) (lcOf g B x v) := by
  simp only [dRicPhi] at *
  ring

end Work.Diff.Evol
