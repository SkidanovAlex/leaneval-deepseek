import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.contMDiff_rmP_fields
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Toolkit for `Work.Diff.GE.roughLap_eq_rot` (tensoriality of `∇Rm` and `∇²Rm`)

## The goal this serves

`Work.Diff.PP.roughLap g x e i j k l = ∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)` is the
trace `ΔRm = tr_g ∇²Rm` of the `(0,6)`-tensor `∇²Rm`, computed in the frame `e`.  Because `∇²Rm` is
a tensor, this trace is a `(0,4)`-tensor, so when the frame is changed by an orthogonal matrix `A`
(`e' i = ∑ j, A i j • e j`) the components transform by `Submission.Diff.Alg.rot A`:

`roughLap g x e' = rot A (roughLap g x e)`   (`Work.Diff.GE.roughLap_eq_rot`).

## The architecture of the proof

`cov2Rm g x u v a b c d = (∇_u ∇Rm)(v,a,b,c,d)` is defined with the `Classical.epsilon`-chosen
extensions `smoothExt x ·` of its arguments.  Proving the displayed identity therefore needs

1. **tensoriality of `∇Rm`**: `covRm g x v a b c d` is `ℝ`-multilinear in `v,a,b,c,d` (`∇Rm` is a
   tensor) — the per-slot linearities `covRm_linear_snd` (2nd slot), `covRm_linear_thd` (3rd),
   `covRm_linear_fth` (4th) are already proved in `Submission/Work/Diff/GE/`, and the first and
   fifth slots are the `Prop`s `CovRmLinFst` / `CovRmLinFith` below;

2. **smoothness of the integrand** `y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` for smooth fields
   (`CovRmFieldSmooth` below) — needed because `mvfderiv I (fun y ↦ …) x u` can only be split over
   sums/products of functions (`mvfderiv_add`, `mvfderiv_mul`) when the functions are differentiable;

3. **tensoriality of `∇²Rm`**: `Submission.Diff.cov2Rm g x` is `ℝ`-multilinear in its six arguments
   (`cov2Rm_linear_fst`, … , `cov2Rm_linear_sixth`), which is the same statement as the fact that
   `∇²Rm` does not depend on the chosen extensions;

4. **the algebraic trace computation** (`roughLap_rot_abstract`).

The `Prop`s below are the *interface* between layer 1/2 and layer 3: the six linearities of
`cov2Rm` are pure `mvfderiv`/`lcOf` bookkeeping and are stated with the layer-1/2 facts as
hypotheses, so that the layer-3 proofs do not depend on how those facts are established.  The
layer-1/2 facts themselves are proved in the sibling modules `covRm_linear_fst`,
`covRm_linear_fith`, `dRmPhi_bind_slotD`, `covRm_field_smooth` of this directory.

## Useful facts already in the repository (all `sorry`-free)

* `Submission.Diff.covRm`, `Submission.Diff.cov2Rm`, `Work.Diff.GE.dRmPhi`,
  `Work.Diff.GE.cov2RmExt`, `Work.Diff.GE.smoothExt`, `Work.Diff.GE.smoothExt_cmdiff`,
  `Work.Diff.GE.smoothExt_apply` (the last two also work with `Work.Diff.Evol.smoothExt_cmdiff`? no:
  `smoothExt` is `Submission.Diff.smoothExt`, its API is in `Work.Diff.GE.Frame`).
* `Work.Diff.GE.covRm_eq_dRmPhi` : `covRm g x v a b c d = dRmPhi g x v (smoothExt x a) … `.
* `Work.Diff.GE.dRmPhi_bind_fst`, `dRmPhi_bind_slotB`, `fth_dRmPhi_bind` : the first three *field*
  slots of `dRmPhi` depend only on the value of the field at the base point.
* `Work.Diff.GE.rmP_add_fst/snd/thd/fth`, `rmP_smul_fst/snd/thd/fth`, `rmP_sum_fst/snd/thd/fth`
  (pointwise linearity of `rmP`), `Work.Diff.GE.rmP_fields_smooth` (smoothness of
  `y ↦ rmP g y (A y) (B y) (C y) (D y)`).
* `Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero` : a smooth
  field vanishing at `x` is a finite sum `∑ i, f i • Y i` with `f i x = 0` (the standard tool for
  "depends only on the value at `x`").
* `Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff` : `y ↦ mvfderiv I F y (V y)` is
  smooth when `F` and `V` are.
* `Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply` : smoothness of
  `y ↦ cov σ y (X y)`.
* `Work.Diff.GE.cmDiff_sum_smul` (`dRmPhi_slotA.lean`) : finite sums of smooth fields are smooth.
* `IsCovariantDerivativeOn.add`, `.leibniz`, `.smul_const` (Mathlib) for `(lcOf g).isCovariantDerivativeOn`,
  and `CovariantDerivative.congr_of_eventuallyEq` for the germ-dependence of `lcOf`.
* `TensorialAt` / `TensorialAt.pointwise` / `TensorialAt.mkHom` (Mathlib,
  `Mathlib.Geometry.Manifold.VectorBundle.Tensoriality`) : the abstract tensoriality criterion; a
  convenient way to package "depends only on the value at `x`" plus linearity in that value.
* `Work.Diff.GE.cov2Rm` (in `NablaRm.lean`) is `Submission.Diff.cov2Rm` (definitionally after
  unfolding `Work.Diff.GE.cov2RmExt` and `smoothExt_apply`), and `Work.Diff.PP.cov2Rm`
  (`Submission/Work/Diff/PP/evolution.lean`) is the same expression again.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.RL

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The fourth field slot of `Work.Diff.GE.dRmPhi` depends only on the value of the field at the
base point: if two smooth fields agree at `x` then `dRmPhi` takes the same value on them. -/
abbrev DRmPhiBindD (g : SMet I M) : Prop :=
  ∀ (x : M) (v : TangentSpace I x) (A B C D D' : Π y : M, TangentSpace I y),
    CMDiff ∞ (T% A) → CMDiff ∞ (T% B) → CMDiff ∞ (T% C) →
    CMDiff ∞ (T% D) → CMDiff ∞ (T% D') → D x = D' x →
    Work.Diff.GE.dRmPhi g x v A B C D = Work.Diff.GE.dRmPhi g x v A B C D'

/-- `covRm = ∇Rm` is `ℝ`-linear in its first vector argument. -/
abbrev CovRmLinFst (g : SMet I M) : Prop :=
  ∀ (x : M) (r s : ℝ) (v₁ v₂ a b c d : TangentSpace I x),
    covRm g x (r • v₁ + s • v₂) a b c d
      = r * covRm g x v₁ a b c d + s * covRm g x v₂ a b c d

/-- `covRm = ∇Rm` is `ℝ`-linear in its fifth vector argument. -/
abbrev CovRmLinFith (g : SMet I M) : Prop :=
  ∀ (x : M) (r s : ℝ) (v a b c d₁ d₂ : TangentSpace I x),
    covRm g x v a b c (r • d₁ + s • d₂)
      = r * covRm g x v a b c d₁ + s * covRm g x v a b c d₂

/-- For smooth fields, the section `y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` is `C^∞` (in
particular differentiable at every point, which is what the splitting rules for `mvfderiv` need). -/
abbrev CovRmFieldSmooth (g : SMet I M) : Prop :=
  ∀ (V A B C D : Π y : M, TangentSpace I y),
    CMDiff ∞ (T% V) → CMDiff ∞ (T% A) → CMDiff ∞ (T% B) → CMDiff ∞ (T% C) → CMDiff ∞ (T% D) →
    CMDiff ∞ (fun y : M ↦ covRm g y (V y) (A y) (B y) (C y) (D y))

end Work.Diff.GE.RL
