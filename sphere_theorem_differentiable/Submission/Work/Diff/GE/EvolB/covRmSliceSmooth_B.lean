import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.BoundaryPlans
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.EvolB

/-!
# Time-smoothness of the `∇Rm` slice along a jointly smooth metric family (copy)

Given a family of metrics `G` jointly smooth on an *open* set `J ∋ t₀` and fixed tangent vectors
`v a b c d` at `x`, the scalar function `t ↦ covRm (G t) x v a b c d` is `C^∞` at `t₀`.

**Route** (the fields are the fixed smooth extensions `smoothExt x ·`):
* `Work.Diff.EXT.covK_familySmooth` (proved, `Submission/Work/Diff/EXT/covK_familySmooth.lean`)
  gives joint `C^∞`-smoothness of `(t,y) ↦ covKRmExt (G t) k (Vf t) (A t) (B t) (C t) (D t) y` on
  `V = J ×ˢ univ` for jointly smooth families of tangent fields; constant families of globally smooth
  fields are jointly smooth (`Work.Diff.EXT.jointField_const`), and
  `JointSmooth G J` *is* `JointMet G (J ×ˢ univ)` definitionally;
* the level-one bridge `Work.Diff.EXT.covKRmExt_one_eq_covRm` (proved, in
  `Submission/Work/Diff/EXT/lapCovKRm_one_eq_lapCovRmAt.lean`) identifies `covKRmExt · 1` with
  `covRm` on smooth fields on the values;
* `ContMDiffOn` on the open set `V` gives `ContMDiffAt` at `(t₀,x)`; composing with the smooth map
  `t ↦ (t,x)` (`ContMDiffAt.comp` with `contMDiffAt_id.prodMk contMDiffAt_const`) and using
  `ContMDiffAt.contDiffAt` gives the claim.

A pedestrian alternative route (if the tower is awkward): unfold
`covRm = mvfderiv (y ↦ rmP (G t) y …) x v − Σ_slots rmP (G t) x (lcOf (G t) (slot) x v) …`,
use `Work.Diff.GE.rmP_jointSmoothNoCompact` for the inner function and
`Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` for the derivative, with the connection corrections
handled by expanding `lcOf (G t) A x v` in a fixed basis via
`Work.Diff.T.lcOf_apply_inner_koszul` plus `Work.Diff.GE.koszul_pairing_jointSmooth` (whose proof
only needs the smooth level).
-/
theorem covRmSliceSmooth_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ}
    (hJ : IsOpen J) (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (v a b c d : TangentSpace I x) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ ↦ Submission.Diff.covRm (G t) x v a b c d) t₀ := by
  -- the open set `V = J ×ˢ univ`, on which the metric family is jointly smooth
  have hV : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hGmet : Work.Diff.EXT.JointMet (I := I) (M := M) G (J ×ˢ (univ : Set M)) := hG
  -- the constant families of the fixed smooth extensions are jointly smooth
  have hJf : ∀ u : TangentSpace I x, Work.Diff.EXT.JointField (I := I) (M := M)
      (fun _ : ℝ => Submission.Diff.smoothExt x u) (J ×ˢ (univ : Set M)) := fun u =>
    (Work.Diff.EXT.jointField_const (I := I) (M := M)
      (Work.Diff.GE.smoothExt_cmdiff x u)).mono (Set.subset_univ _)
  -- joint smoothness of the level-one tower on `V`
  have hsm := Work.Diff.EXT.covK_familySmooth (I := I) (M := M) hLC (V := J ×ˢ (univ : Set M))
    hV hGmet 1 (Vf := fun _ (_ : Fin 1) => Submission.Diff.smoothExt x v)
    (fun i => hJf v) (A := fun _ : ℝ => Submission.Diff.smoothExt x a)
    (B := fun _ : ℝ => Submission.Diff.smoothExt x b)
    (C := fun _ : ℝ => Submission.Diff.smoothExt x c)
    (D := fun _ : ℝ => Submission.Diff.smoothExt x d)
    (hJf a) (hJf b) (hJf c) (hJf d)
  have hAt : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Work.Diff.EXT.covKRmExt (G p.1) 1
        (fun _ : Fin 1 => Submission.Diff.smoothExt x v)
        (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
        (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) p.2) (t₀, x) :=
    hsm.contMDiffAt (hV.mem_nhds ⟨ht₀, mem_univ x⟩)
  -- slice at `x`
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => Work.Diff.EXT.covKRmExt (G t) 1
        (fun _ : Fin 1 => Submission.Diff.smoothExt x v)
        (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
        (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x) t₀ :=
    hAt.comp t₀ (contMDiffAt_id.prodMk contMDiffAt_const)
  -- level one is `∇Rm` on the values
  have hfun : (fun t : ℝ => Work.Diff.EXT.covKRmExt (G t) 1
        (fun _ : Fin 1 => Submission.Diff.smoothExt x v)
        (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
        (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x)
      = fun t : ℝ => Submission.Diff.covRm (G t) x v a b c d := by
    funext t
    rw [← Work.Diff.EXT.covKRm_one (g := G t) x v a b c d]
    rfl
  rw [hfun] at hcomp
  exact hcomp.contDiffAt

end Work.Diff.GE.EvolB
