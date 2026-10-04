import Mathlib
import Submission.Work.Diff.GE.scal_lapl_defs
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **The first derivative of `∇Rm` on five smooth fields.**

`y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` is the `(0,5)`-tensor `∇Rm` evaluated on the fields
`V A B C D`; its derivative in the direction `v` is, by the Leibniz rule for the covariant
derivative, `(∇_v ∇Rm)(V,A,B,C,D)` plus the five corrections coming from the connection acting on
the five fields.  The frozen `Submission.Diff.cov2Rm` is exactly `(∇_v ∇Rm)` computed with the
`Classical.epsilon`-chosen smooth extensions `smoothExt x ·` of the values at `x`, so the statement
is the rearrangement of the *definition* of `Work.Diff.GE.cov2RmExt` — the only mathematical input
being the value-dependence of `cov2RmExt` in its five field slots
(`Work.Diff.GE.kato_cov2RmExt_field`, which identifies the expression computed with `V A B C D` and
with the canonical extensions `smoothExt x (V x), …`). -/
theorem mvfderiv_covRm_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {V A B C D : Π y : M, TangentSpace I y}
    (hV : Work.Diff.GE.SmoothSect (I := I) (M := M) V)
    (hA : Work.Diff.GE.SmoothSect (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothSect (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothSect (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothSect (I := I) (M := M) D)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ Submission.Diff.covRm g y (V y) (A y) (B y) (C y) (D y)) x v
      = Submission.Diff.cov2Rm g x v (V x) (A x) (B x) (C x) (D x)
        + Submission.Diff.covRm g x (Submission.Diff.lcOf g V x v) (A x) (B x) (C x) (D x)
        + Submission.Diff.covRm g x (V x) (Submission.Diff.lcOf g A x v) (B x) (C x) (D x)
        + Submission.Diff.covRm g x (V x) (A x) (Submission.Diff.lcOf g B x v) (C x) (D x)
        + Submission.Diff.covRm g x (V x) (A x) (B x) (Submission.Diff.lcOf g C x v) (D x)
        + Submission.Diff.covRm g x (V x) (A x) (B x) (C x) (Submission.Diff.lcOf g D x v) := by
  -- `Submission.Diff.cov2Rm` on the values is `Work.Diff.GE.cov2RmExt` on the same five fields.
  have hb : Submission.Diff.cov2Rm g x v (V x) (A x) (B x) (C x) (D x)
      = Work.Diff.GE.cov2RmExt g x v V A B C D := by
    rw [show Submission.Diff.cov2Rm g x v (V x) (A x) (B x) (C x) (D x)
        = Work.Diff.GE.cov2RmExt g x v (Submission.Diff.smoothExt x (V x))
            (Submission.Diff.smoothExt x (A x)) (Submission.Diff.smoothExt x (B x))
            (Submission.Diff.smoothExt x (C x)) (Submission.Diff.smoothExt x (D x)) from by
          simp only [Work.Diff.GE.cov2RmExt, Submission.Diff.cov2Rm, Work.Diff.GE.smoothExt_apply]]
    -- `cov2RmExt` depends on its five field slots only through the values at `x`.
    exact (kato_cov2RmExt_field (I := I) (M := M) hLC g x
      (Submission.Diff.smoothExt x (V x)) (Submission.Diff.smoothExt x (A x))
      (Submission.Diff.smoothExt x (B x)) (Submission.Diff.smoothExt x (C x))
      (Submission.Diff.smoothExt x (D x)) V A B C D
      (smoothExt_cmdiff x (V x)) (smoothExt_cmdiff x (A x)) (smoothExt_cmdiff x (B x))
      (smoothExt_cmdiff x (C x)) (smoothExt_cmdiff x (D x)) hV hA hB hC hD
      (smoothExt_apply x (V x)) (smoothExt_apply x (A x)) (smoothExt_apply x (B x))
      (smoothExt_apply x (C x)) (smoothExt_apply x (D x))).1 v
  -- Unfolding the definition of `cov2RmExt` at `v` then gives the claimed rearrangement.
  rw [hb]
  unfold Work.Diff.GE.cov2RmExt
  ring

end Work.Diff.GE
