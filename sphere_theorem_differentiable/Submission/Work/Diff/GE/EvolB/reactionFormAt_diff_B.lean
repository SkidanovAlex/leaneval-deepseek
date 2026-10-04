import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.EvolB.frame_indep_B
import Submission.Work.Diff.GE.contMDiff_rmP_fields
import Submission.Work.Diff.GE.onFrameONfield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability of the reaction form on smooth fields (`EvolB`)

`Work.Diff.GE.EvolB.reactionFormAt_diff_B` is the smooth-level version of
`Work.Diff.GE.reactionFormAt_diff` (which is stated for an *analytic* manifold): the contraction
`y ↦ reactionFormAt F g y (A y) (B y) (C y) (D y)` is `C^∞` (hence `MDifferentiableAt`) whenever
`g` is a smooth metric, `A,B,C,D` are smooth fields and `F` is `C^∞` and commutes with the
orthogonal action.  It is needed for the split of
`mvfderiv I (fun y ↦ lapRmAt (G t) y (A y) … + reactionFormAt reactionMap (G t) y (A y) …) x v`
in the assembly of the fixed-vector `∇Rm` evolution.

The proof is the one of `Work.Diff.GE.Rfa.reactionW_contMDiffAt` (transcribed here at the smooth
level, in the `Rxn` namespace, using `Work.Diff.GE.onFrameONfield` for the smooth orthonormal frame
family and `Work.Diff.GE.EvolB.frame_indep_B` for the frame independence).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- The metric pairing of two smooth sections is `C^∞` (the frozen `SMet` pairing is
definitionally the instance one for `⟨g.toRiemannianMetric⟩`). -/
theorem contMDiffAt_inner_fields_B (g : SMet I M)
    {X Y : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothField M X) (hY : Work.Diff.GE.SmoothField M Y) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y : M ↦ g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hX' : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun m : M => (⟨m, X m⟩ : Bundle.TotalSpace E (TangentSpace I))) x := hX.contMDiffAt
  have hY' : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun m : M => (⟨m, Y m⟩ : Bundle.TotalSpace E (TangentSpace I))) x := hY.contMDiffAt
  exact ContMDiffAt.inner_bundle (IB := I) (IM := I) (F := E)
    (E := (fun x : M => TangentSpace I x)) (b := fun m : M => m) (v := X) (w := Y) hX' hY'

/-- The curvature array in a frame field is `C^∞`. -/
theorem contMDiffAt_rmFrameField_B (hLC : LCSmooth I M) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.SmoothField M (W i)) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => Work.Diff.GE.Rxn.rmFrameField g (fun y i => W i y) y) x := by
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

/-- The contraction of `F (Rm)` with four smooth fields in a smooth frame field is `C^∞`. -/
theorem reactionW_contMDiffAt_B (hLC : LCSmooth I M)
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F)
    (g : SMet I M) (W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.SmoothField M (W i))
    (A B C D : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField M A) (hB : Work.Diff.GE.SmoothField M B)
    (hC : Work.Diff.GE.SmoothField M C) (hD : Work.Diff.GE.SmoothField M D) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => Work.Diff.GE.Rxn.reactionW F g (fun y i => W i y) A B C D y) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hrm : ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => Work.Diff.GE.Rxn.rmFrameField g (fun y i => W i y) y) x :=
    contMDiffAt_rmFrameField_B (I := I) (M := M) hLC g W hW x
  have hFrm : ContMDiffAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => F (Work.Diff.GE.Rxn.rmFrameField g (fun y i => W i y) y)) x :=
    (hF.contMDiff.contMDiffAt).comp x hrm
  have hcomp : ∀ i j k l : Fin (Module.finrank ℝ E), ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (Work.Diff.GE.Rxn.rmFrameField g (fun y i => W i y) y)) i j k l) x := by
    intro i j k l
    exact contMDiffAt_pi_space.mp
      (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hFrm i) j) k) l
  have hpair : ∀ (i : Fin (Module.finrank ℝ E)) (Y : Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothField M Y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y : M => g.inner y (W i y) (Y y)) x :=
    fun i Y hY => contMDiffAt_inner_fields_B (I := I) (M := M) g (hW i) hY x
  change ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
    (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l,
      (g.inner y (W i y) (A y) * g.inner y (W j y) (B y) * g.inner y (W k y) (C y)
        * g.inner y (W l y) (D y)) * (F (Work.Diff.GE.Rxn.rmFrameField g (fun y i => W i y) y))
          i j k l) x
  refine ContMDiffAt.sum (t := Finset.univ) (fun i _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun j _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun k _ => ?_)
  refine ContMDiffAt.sum (t := Finset.univ) (fun l _ => ?_)
  refine ContMDiffAt.mul ?_ (hcomp i j k l)
  refine ContMDiffAt.mul ?_ (hpair l D hD)
  refine ContMDiffAt.mul ?_ (hpair k C hC)
  exact ContMDiffAt.mul (hpair i A hA) (hpair j B hB)

/-- **Differentiability of the reaction form on smooth fields.** -/
theorem reactionFormAt_diff_B
    (hLC : LCSmooth I M)
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F)
    (hE : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Curv4 (Module.finrank ℝ E),
        F (rot A R) = rot A (F R)) :
    ∀ (g : SMet I M) (x : M) (A B C D : Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothField M A → Work.Diff.GE.SmoothField M B →
      Work.Diff.GE.SmoothField M C → Work.Diff.GE.SmoothField M D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.reactionFormAt F g y (A y) (B y) (C y) (D y)) x := by
  intro g x A B C D hA hB hC hD
  obtain ⟨W, hW, hWON, -⟩ := Work.Diff.GE.onFrameONfield (I := I) (M := M) hLC g x
  have hsmooth : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => Work.Diff.GE.Rxn.reactionW F g (fun y i => W i y) A B C D y) x :=
    reactionW_contMDiffAt_B (I := I) (M := M) hLC F hF g W hW A B C D hA hB hC hD x
  have hdiff : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => Work.Diff.GE.Rxn.reactionW F g (fun y i => W i y) A B C D y) x :=
    hsmooth.mdifferentiableAt (by simp)
  refine hdiff.congr_of_eventuallyEq ?_
  filter_upwards [hWON] with y hy
  rw [show Work.Diff.GE.Rxn.reactionW F g (fun y i => W i y) A B C D y
      = Work.Diff.GE.Rxn.reactionFormAtE F g y (fun i => W i y) (A y) (B y) (C y) (D y)
      from rfl,
    Work.Diff.GE.Rxn.reactionFormAt_eq_reactionFormAtE]
  exact frame_indep_B (I := I) (M := M) hLC F hE g y
    (fun i => W i y) (Submission.Diff.onFrame g y) hy
    (Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g y)
    (A y) (B y) (C y) (D y)

end Work.Diff.GE.EvolB
