/-
# Vocabulary for gluing local chart data of a metric family into a global one

This file prepares the construction used by `Work.Diff.EXT.glue_local_metric_families`.  The
problem solved there is the following: given a family of smooth metrics `G t` on `M`, jointly
smooth on `[0,T)`, and for every chart centre `x₀` a *local smooth extension of the chart matrix*
of `G` past `t = T` (the hypothesis `hV`), build a family of metrics `H₁` jointly smooth on a
two-sided time interval around `T` and agreeing with `G` on the left.

The construction produces, for each chart centre `x₀`, a local *form* on the tangent bundle whose
matrix in the coordinate frame of the chart at `x₀` is a prescribed `MatE`-valued function.  The
notions here are:

* `frameCoords x₀ x : TangentSpace I x →L[ℝ] E`, the coordinates of a tangent vector in the
  coordinate frame of the chart at `x₀` (the inverse of `frameVector x₀ x`);
* `frameCoord x₀ x i`, the `i`-th coordinate functional;
* `formInFrame x₀ x A`, the continuous bilinear form on `TangentSpace I x` whose matrix in the
  frame at `x₀` is `A`;
* `frameMat x₀ x φ`, the matrix of a form `φ` in the frame at `x₀` (the inverse operation);
* `FormFam I M`, an abbreviation for a time-dependent family of such forms, and
  `formFamSection γ`, its total-space representation as a section of the bundle of bilinear forms.

The lemmas proved here are the algebraic ones: `formInFrame_apply` (the value of `formInFrame` in
terms of the coordinate functionals), `formInFrame_apply_basis` (its matrix is the prescribed one)
and `formInFrame_apply_self` (its diagonal values, which govern positivity).
-/

import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.bilinMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The coordinates of a tangent vector in the coordinate frame of the chart at `x₀`: the
continuous linear map inverse to `frameVector x₀ x` on the base set of the chart. -/
noncomputable def frameCoords (x₀ x : M) : TangentSpace I x →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x

/-- The `i`-th coordinate functional of the frame of the chart at `x₀`. -/
noncomputable def frameCoord (x₀ x : M) (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((bB (E := E)).coord i)).comp (frameCoords (I := I) x₀ x)

/-- **The bilinear form with prescribed matrix in the frame of the chart at `x₀`.** -/
noncomputable def formInFrame (x₀ x : M) (A : MatE (E := E)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    A i j • ((frameCoord (I := I) x₀ x i).smulRight (frameCoord (I := I) x₀ x j))

/-- The matrix of a bilinear form in the frame of the chart at `x₀`. -/
noncomputable def frameMat (x₀ x : M)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : MatE (E := E) :=
  fun i j => φ (Submission.Geodesic.frameVector (I := I) x₀ x (bB (E := E) i))
    (Submission.Geodesic.frameVector (I := I) x₀ x (bB (E := E) j))

lemma frameCoord_apply (x₀ x : M) (i : Fin (Module.finrank ℝ E)) (u : TangentSpace I x) :
    frameCoord (I := I) x₀ x i u
      = ((bB (E := E)).coord i) (frameCoords (I := I) x₀ x u) := rfl

/-- **The value of `formInFrame` in terms of the coordinate functionals.** -/
theorem formInFrame_apply (x₀ x : M) (A : MatE (E := E)) (u v : TangentSpace I x) :
    formInFrame (I := I) x₀ x A u v =
      ∑ i, ∑ j, A i j * ((bB (E := E)).coord i) (frameCoords (I := I) x₀ x u) *
        ((bB (E := E)).coord j) (frameCoords (I := I) x₀ x v) := by
  simp only [formInFrame, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    frameCoord_apply, smul_eq_mul]
  ring_nf

/-- A time-dependent family of bilinear forms on the tangent bundle of `M`. -/
abbrev FormFam (I : ModelWithCorners ℝ E H') (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] :=
  ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/-- The total-space representation of a family of bilinear forms, as a section of the bundle of
bilinear forms over `M` pulled back to `ℝ × M` along `Prod.snd`. -/
noncomputable def formFamSection (γ : FormFam (I := I) (M := M)) :
    ℝ × M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  fun p => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) p.2 (γ p.1 p.2)

/-- Smoothness of a family of bilinear forms on a time set.  For a family of metrics
`F : ℝ → SMet I M`, this is *definitionally* `Submission.Diff.JointSmooth F J` for
`γ := fun t x => (F t).inner x`. -/
def FormFamJoint (γ : FormFam (I := I) (M := M)) (J : Set ℝ) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) (I.prod (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
    (formFamSection γ) (J ×ˢ (univ : Set M))

/-- `JointSmooth` of a family of metrics is `FormFamJoint` of its inner products. -/
theorem jointSmooth_iff_formFamJoint {F : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} :
    Submission.Diff.JointSmooth F J ↔
      FormFamJoint (I := I) (fun t x => (F t).inner x) J := Iff.rfl

end Work.Diff.EXT
