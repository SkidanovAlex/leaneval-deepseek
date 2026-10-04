import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.Diff.GE.reactionFormAt_diff`

The frozen object `Work.Diff.GE.reactionFormAt F g x a b c d` evaluates the `(0,4)`-tensor
`F (Rm g x)` on four vectors `a b c d`, using the `Classical.epsilon`-chosen orthonormal frame
`onFrame g x` at `x`.  That frame jumps with `x`, so `reactionFormAt` is not *a priori* a smooth
function of `x`; it only becomes one after using the equivariance of `F` under orthogonal changes of
frame to replace `onFrame g x` by a smoothly varying orthonormal frame.

This file collects the definitions used by that argument:

* `reactionFormAtE F g x e a b c d` -- the same contraction evaluated in an *explicit* frame `e`;
  `reactionFormAt` is the special case `e = onFrame g x` (`reactionFormAt_eq_reactionFormAtE`);
* `rmFrameField g W y` -- the curvature array of `g` at `y` in the frame `fun i => W i y`, for a
  family `W` of sections (so that `y ↦ rmFrameField g W y` can be smooth);
* `reactionW F g W A B C D y` -- the reaction form evaluated in the frame field `W` on the four
  field slots `A B C D`, as a function of the base point;
  `reactionW F g W A B C D y = reactionFormAtE F g y (fun i => W i y) (A y) (B y) (C y) (D y)`.

Nothing here is a mathematical statement beyond the two definitional unfoldings.

## Hints for the lemmas proved about these definitions

* Frame change of the curvature components: `Work.Diff.GE.rmFrame_eq_rot`
  (`Submission/Work/Diff/GE/rmFrame_eq_rot.lean`): if `e' i = ∑ j, A i j • e j` then
  `rmFrame g x e' = rot A (rmFrame g x e)`; it needs `hLC : LCSmooth I M` and only the expansion,
  not orthonormality.
* Contraction identity for `rot`: `Work.Diff.GE.rot_contract`
  (`Submission/Work/Diff/GE/rot_contract.lean`): for `A ∈ Matrix.orthogonalGroup`,
  `∑ p q, rot A φ i j p q * rot A ψ k l p q = ∑ a b c d, A i a * A j b * A k c * A l d *
  (∑ p q, φ a b p q * ψ c d p q)`.
* Smoothness of the curvature components along smooth fields: `Work.Diff.GE.contMDiff_rmP_fields`
  (`Submission/Work/Diff/GE/contMDiff_rmP_fields.lean`, sorry-free):
  `SmoothField A → SmoothField B → SmoothField C → SmoothField D → CMDiff ∞ (fun y => rmP g y
  (A y) (B y) (C y) (D y))`, for `g : SMet I M` and `hLC : LCSmooth I M`.
* Pairing smooth sections: `ContMDiffAt.inner_bundle` (`Mathlib`) with the instance
  `letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩`
  (so that the instance inner product *is* `g.inner`; see `Work.Diff.GE.inner_eq_metric`).
* A smooth local field of orthonormal frames: `Work.Diff.GE.smooth_onframe`
  (`Submission/Work/Diff/GE/smooth_onframe.lean`) -- but note that this module and
  `Submission/Work/Diff/GE/curvbasic.lean` both declare `Work.Diff.GE.exists_isONFrame` and
  `Work.Diff.GE.isONFrame_onFrame`, so no file may import both `smooth_onframe` and `curvbasic`
  (nor `bianchi_kato_defs`, which also duplicates those names). The modules
  `ReactionDefs`, `NablaRm`, `Frame`, `curvbasic`, `contMDiff_rmP_fields`, `rmFrame_eq_rot`,
  `rot_contract` are mutually compatible; the `smooth_onframe` / `bianchi_kato_defs` / `dRmPhi`
  family is not compatible with them.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.Rfa

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section `X` of the tangent bundle is `C^∞` on the set `U` (plain-name form of
`CMDff[U] ∞ (T% X)`, so that it can be used in delegated statements without opening the
`Manifold` scope). -/
abbrev SmoothFieldOn (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (U : Set M) (X : Π y : M, TangentSpace I y) : Prop :=
  CMDiff[U] ∞ (T% X)

/-- The reaction form `F(Rm)` of `g` at `x`, evaluated on four vectors, in an *explicit* frame `e`:
the fourfold contraction of `F (rmFrame g x e)` with the coefficients
`g.inner x (e i) a`, `g.inner x (e j) b`, `g.inner x (e k) c`, `g.inner x (e l) d`. -/
noncomputable def reactionFormAtE (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : TangentSpace I x) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (e i) a * g.inner x (e j) b * g.inner x (e k) c * g.inner x (e l) d)
      * (F (rmFrame g x e)) i j k l

/-- `reactionFormAt` is `reactionFormAtE` computed in the chosen frame `onFrame g x`. -/
lemma reactionFormAt_eq_reactionFormAtE
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    reactionFormAt F g x a b c d = reactionFormAtE F g x (onFrame g x) a b c d := rfl

/-- The curvature array of `g` at `y` in the frame `fun i => W i y`. -/
noncomputable def rmFrameField (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) (y : M) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => rmP g y (W i y) (W j y) (W k y) (W l y)

/-- `rmFrameField` is `rmFrame` in the frame `fun i => W i y`. -/
lemma rmFrameField_eq (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) (y : M) :
    rmFrameField g W y = rmFrame g y (fun i => W i y) := rfl

/-- The reaction form evaluated in the frame field `W` on the four field slots `A B C D`, as a
function of the base point. -/
noncomputable def reactionW (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (A B C D : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner y (W i y) (A y) * g.inner y (W j y) (B y) * g.inner y (W k y) (C y)
      * g.inner y (W l y) (D y)) * (F (rmFrameField g W y)) i j k l

/-- `reactionW` is `reactionFormAtE` in the frame `fun i => W i y`. -/
lemma reactionW_eq_reactionFormAtE
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (A B C D : Π y : M, TangentSpace I y) (y : M) :
    reactionW F g W A B C D y
      = reactionFormAtE F g y (fun i => W i y) (A y) (B y) (C y) (D y) := rfl

end Work.Diff.GE.Rfa
