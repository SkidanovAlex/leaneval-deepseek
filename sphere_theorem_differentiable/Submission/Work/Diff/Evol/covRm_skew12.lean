import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.Evol.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- `mvfderiv` of the pointwise negative of a function. -/
private theorem mvfderiv_neg_apply (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => -F y) x v = -mvfderiv I F x v := by
  rw [show (fun y : M => -F y) = -F from rfl, mvfderiv_neg]
  simp

/-- `dRmPhi` (the section-level form of `∇Rm`) is antisymmetric in its first two field slots. -/
private theorem dRmPhi_skew12 (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y) :
    Work.Diff.GE.dRmPhi g x v A B C D = -Work.Diff.GE.dRmPhi g x v B A C D := by
  have hfun : (fun y : M => rmP g y (B y) (A y) (C y) (D y))
      = -(fun y : M => rmP g y (A y) (B y) (C y) (D y)) :=
    funext fun y => Work.Diff.GE.rmP_antisymm hLC g y (B y) (A y) (C y) (D y)
  have h1 : mvfderiv I (fun y : M => rmP g y (B y) (A y) (C y) (D y)) x v
      = -mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v := by
    rw [hfun]
    exact mvfderiv_neg_apply (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
  have c2 : rmP g x (lcOf g B x v) (A x) (C x) (D x)
      = -rmP g x (A x) (lcOf g B x v) (C x) (D x) :=
    Work.Diff.GE.rmP_antisymm hLC g x (lcOf g B x v) (A x) (C x) (D x)
  have c3 : rmP g x (B x) (lcOf g A x v) (C x) (D x)
      = -rmP g x (lcOf g A x v) (B x) (C x) (D x) :=
    Work.Diff.GE.rmP_antisymm hLC g x (B x) (lcOf g A x v) (C x) (D x)
  have c4 : rmP g x (B x) (A x) (lcOf g C x v) (D x)
      = -rmP g x (A x) (B x) (lcOf g C x v) (D x) :=
    Work.Diff.GE.rmP_antisymm hLC g x (B x) (A x) (lcOf g C x v) (D x)
  have c5 : rmP g x (B x) (A x) (C x) (lcOf g D x v)
      = -rmP g x (A x) (B x) (C x) (lcOf g D x v) :=
    Work.Diff.GE.rmP_antisymm hLC g x (B x) (A x) (C x) (lcOf g D x v)
  simp only [Work.Diff.GE.dRmPhi]
  rw [h1, c2, c3, c4, c5]
  ring

/-- **Antisymmetry of `∇Rm` in its first two slots.**  `(∇_v Rm)(a,b,c,d) = - (∇_v Rm)(b,a,c,d)`.

Companion of `Work.Diff.Evol.covRm_pair`; it follows from `Submission.Work.Diff.GE.rmP_antisymm`
(`rmP g x a b c d = - rmP g x b a c d`) propagated through the four connection corrections of `dRmPhi`,
exactly as `Work.Diff.GE.covRm_skew_last` does it for the last two slots (unfold `covRm_eq_dRmPhi` on
both sides, `mvfderiv_neg` for the derivative term, `rmP_antisymm` for each correction).
Stay in the chain of `curvbasic`: do NOT import
`Submission/Work/Diff/GE/bianchi_kato_defs.lean` or `.../dRSec_bianchi.lean` (name clashes).
State the manifold hypothesis at the SMOOTH level, as written. -/
theorem covRm_skew12
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Submission.Diff.covRm g x v a b c d = - Submission.Diff.covRm g x v b a c d := by
  rw [Work.Diff.GE.covRm_eq_dRmPhi (a := a) (b := b) (c := c) (d := d),
      Work.Diff.GE.covRm_eq_dRmPhi (a := b) (b := a) (c := c) (d := d)]
  exact dRmPhi_skew12 hLC g x v (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)

end Work.Diff.Evol
