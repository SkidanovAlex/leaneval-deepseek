import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.Rfa.Defs
import Submission.Work.Diff.GE.exists_global_ON_frame
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.GE.Rfa.reactionW_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability of the reaction form (assembly)

`Work.Diff.GE.reactionFormAt F g y (A y) (B y) (C y) (D y)` is the `(0,4)`-tensor `F (Rm g y)` of the
metric `g` contracted with four smooth tangent fields.  Although the *definition* expands this
contraction in the `Classical.epsilon`-chosen orthonormal frame `onFrame g y` of `T_yM` -- a frame
which depends on `y` in a completely arbitrary (non-measurable) way -- the *value* is a smooth
function of `y`, because `F` is equivariant under orthogonal changes of frame
(`hE : F (rot A R) = rot A (F R)`) and hence the contraction does not depend on the choice of the
orthonormal frame.

The proof is therefore an instance of "unfold the definition in a smoothly varying frame":

1. `Work.Diff.GE.exists_global_ON_frame` gives globally `C^∞` fields `W i` which are a
   `g`-orthonormal frame of `T_yM` for all `y` near `x`;
2. `Work.Diff.GE.Rfa.reactionW_contMDiffAt` says that the same contraction evaluated in the frame
   field `W` is `C^∞` at `x` (this is where the curvature `y ↦ F (Rm g y)` is differentiated, via
   `Work.Diff.GE.contMDiff_rmP_fields`);
3. `Work.Diff.GE.Rfa.reactionFormAtE_frame_indep` (frame independence, from `hE`) shows that the
   two points of view agree on a neighbourhood of `x`: at each `y` both `onFrame g y` and `W · y`
   are orthonormal frames, so the two contractions coincide;
4. `MDifferentiableAt` follows from `ContMDiffAt`.
-/

namespace Work.Diff.GE

theorem reactionFormAt_diff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
        Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hE : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R)) :
    ∀ (g : Submission.Diff.SMet I M) (x : M)
      (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.reactionFormAt F g y (A y) (B y) (C y) (D y)) x := by
  intro g x A B C D hA hB hC hD
  -- a globally smooth family of fields which is an orthonormal frame near `x`
  obtain ⟨W, hW, hWON⟩ := exists_global_ON_frame (I := I) (M := M) g x
  -- the contraction in the frame field `W` is `C^∞`
  have hsmooth : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y : M => Rfa.reactionW F g W A B C D y) x :=
    Rfa.reactionW_contMDiffAt (I := I) (M := M) hLC F hF g W hW A B C D hA hB hC hD x
  have hdiff : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => Rfa.reactionW F g W A B C D y) x :=
    hsmooth.mdifferentiableAt (by simp)
  -- ... and it agrees with the reaction form itself near `x`, by frame independence
  refine hdiff.congr_of_eventuallyEq ?_
  filter_upwards [hWON] with y hy
  rw [Rfa.reactionW_eq_reactionFormAtE, Rfa.reactionFormAt_eq_reactionFormAtE]
  exact Rfa.reactionFormAtE_frame_indep (I := I) (M := M) hLC F hE g y
    (fun i => W i y) (Submission.Diff.onFrame g y) hy
    (Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g y) (A y) (B y) (C y) (D y)

end Work.Diff.GE
