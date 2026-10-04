import Mathlib
import Submission.Work.Diff.GE.Rfa.Defs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of `reactionW`

`Work.Diff.GE.Rfa.reactionW F g W A B C D y` is the reaction form `F (Rm (g) y)` of the metric `g`
evaluated at `y` in the frame field `W` on the four field slots `A B C D` (Defs.lean):

`∑ i j k l, (g.inner y (W i y) (A y) * g.inner y (W j y) (B y) * g.inner y (W k y) (C y)
  * g.inner y (W l y) (D y)) * (F (rmFrameField g W y)) i j k l`.

This file proves that it is `C^∞` at every point, from `hLC : LCSmooth I M`, the smoothness of `F`,
and the smoothness of the sections `W i`, `A`, `B`, `C`, `D`.  Note that `W` is indexed with the
frame index *outside* (`Fin n → Π y, TangentSpace I y`), so `y ↦ W i y` are ordinary smooth fields.

Nothing deep is going on: it is the closure of `C^∞` functions under finite sums and products, with
three ingredients:

* `contMDiffAt_rmFrameField` : `y ↦ rmFrameField g W y` is `C^∞` as a `Curv4 n`-valued map
  (componentwise `Work.Diff.GE.contMDiff_rmP_fields`, assembled with `contMDiffAt_pi_space`);
* `contMDiffAt_inner_fields` : `y ↦ g.inner y (X y) (Y y)` is `C^∞` for smooth fields `X`, `Y`
  (the bridge from the frozen `Submission.Diff.SMet` pairing to the instance inner product used by
  `ContMDiffAt.inner_bundle` -- the same bridge as in
  `Submission/Work/Diff/GE/contMDiff_rmP_fields.lean`);
* `ContMDiffAt` is closed under sums (`ContMDiffAt.sum`) and products (`ContMDiffAt.mul`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.Rfa

/-- **The curvature array in a frame field is `C^∞`.**  For smooth fields `W i` and a smooth
metric `g`, the `Curv4 n`-valued function `y ↦ rmFrameField g W y = (fun i j k l => rmP g y
(W i y) (W j y) (W k y) (W l y))` is `C^∞` at every point.

Componentwise this is exactly `Work.Diff.GE.contMDiff_rmP_fields`; the components are assembled
into the (nested) product `Curv4 n` with `contMDiffAt_pi_space`. -/
theorem contMDiffAt_rmFrameField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.SmoothField (I := I) (M := M) (W i)) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => rmFrameField g W y) x := by
  rw [contMDiffAt_pi_space]
  intro i
  rw [contMDiffAt_pi_space]
  intro j
  rw [contMDiffAt_pi_space]
  intro k
  rw [contMDiffAt_pi_space]
  intro l
  exact (Work.Diff.GE.contMDiff_rmP_fields (I := I) (M := M) hLC g
    (hW i) (hW j) (hW k) (hW l)).contMDiffAt

/-- **The metric pairing of two smooth tangent fields is `C^∞`.**  The frozen interface
`Submission.Diff.SMet` is used explicitly through `g.inner`, while the library lemma
`ContMDiffAt.inner_bundle` speaks about the instance inner product of the Riemannian bundle
`⟨g.toRiemannianMetric⟩`; the two are definitionally equal (hence the bridge is `exact`). -/
theorem contMDiffAt_inner_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : Submission.Diff.SMet I M) {X Y : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothField (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothField (I := I) (M := M) Y) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y : M => g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hX' : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun m : M => (⟨m, X m⟩ : Bundle.TotalSpace E (TangentSpace I))) x := hX.contMDiffAt
  have hY' : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun m : M => (⟨m, Y m⟩ : Bundle.TotalSpace E (TangentSpace I))) x := hY.contMDiffAt
  exact ContMDiffAt.inner_bundle (IB := I) (IM := I) (F := E)
    (E := (fun x : M => TangentSpace I x)) (b := fun m : M => m) (v := X) (w := Y) hX' hY'

theorem reactionW_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.SmoothField (I := I) (M := M) (W i))
    (A B C D : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothField (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothField (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothField (I := I) (M := M) D)
    (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y : M => Work.Diff.GE.Rfa.reactionW F g W A B C D y) x := by
  -- install the metric of `g` as the Riemannian structure, so that `g.inner` becomes `inner ℝ`
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the curvature array and `F` applied to it are smooth
  have hrm : ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => rmFrameField g W y) x := contMDiffAt_rmFrameField hLC g W hW x
  have hFrm : ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => F (rmFrameField g W y)) x :=
    (hF.contMDiff.contMDiffAt).comp x hrm
  -- each component of `F (rmFrameField g W ·)` is a smooth real-valued function
  have hcomp : ∀ i j k l : Fin (Module.finrank ℝ E), ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (rmFrameField g W y)) i j k l) x := by
    intro i j k l
    exact contMDiffAt_pi_space.mp
      (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hFrm i) j) k) l
  -- the metric pairings are smooth
  have hpair : ∀ (i : Fin (Module.finrank ℝ E)) (Y : Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothField (I := I) (M := M) Y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y : M => g.inner y (W i y) (Y y)) x :=
    fun i Y hY => contMDiffAt_inner_fields g (hW i) hY x
  -- unfold `reactionW` and close under finite sums and products
  change ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
    (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l,
      (g.inner y (W i y) (A y) * g.inner y (W j y) (B y) * g.inner y (W k y) (C y)
        * g.inner y (W l y) (D y)) * (F (rmFrameField g W y)) i j k l) x
  refine ContMDiffAt.sum (t := Finset.univ) (fun i _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun j _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun k _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun l _ => ?_)
  refine ContMDiffAt.mul ?_ (hcomp i j k l)
  refine ContMDiffAt.mul ?_ (hpair l D hD)
  refine ContMDiffAt.mul ?_ (hpair k C hC)
  exact ContMDiffAt.mul (hpair i A hA) (hpair j B hB)

end Work.Diff.GE.Rfa
