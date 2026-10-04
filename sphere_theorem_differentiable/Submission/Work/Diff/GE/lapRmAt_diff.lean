import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.exists_ON_frame_field_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability of the rough Laplacian of the curvature along smooth fields

The rough Laplacian `ΔRm = ∑ₘ ∇ₘ∇ₘRm` is defined in the frozen file `Submission/Diff/Grad.lean`
(here `Work.Diff.GE.lapRmAt`) by contracting the second covariant derivative `cov2Rm` of the
curvature over the `Classical.epsilon`-chosen frame `onFrame g x`, which is *not* smooth in `x`.
The present lemma records that, nevertheless, once smooth vector fields `A B C D` are substituted
into the four slots, the resulting **scalar** function of `y` is differentiable (indeed `C^∞`) at
every point.

The proof avoids the non-smooth frame entirely:

* near `x` there is a `g`-orthonormal frame `F ·` whose components are *globally* smooth sections
  (`Work.Diff.GE.exists_global_ON_frame_smooth`, from `exists_ON_frame_field_eq.lean`);
* `Work.Diff.GE.lapRmAt_trace` (frame independence of the trace) computes `lapRmAt` in *any*
  `g`-orthonormal frame, so `lapRmAt g y (A y) … = ∑ᵢ cov2Rm g y (F i y) (F i y) (A y) …` near `x`;
* each summand is `C^∞` at `x`: `Work.Diff.GE.kato_cov2RmExt_field` (proved) gives smoothness of
  `y ↦ cov2RmExt g y (F i y) (F i) A B C D` for globally smooth sections, and the
  `Classical.epsilon` extensions occurring in the *definition* of `cov2Rm` are removed with the
  value-dependence lemmas `cov2RmExt_bind_*`
  (`Submission/Work/Diff/GE/cov2RmExt_prelim.lean`), using that `smoothExt y (v)` is a globally
  smooth field with value `v` at `y`;
* `ΔRm` is a finite sum over `Fin (finrank ℝ E)`, and a finite sum of functions `C^∞` at `x` is
  `C^∞` at `x` (`ContMDiffAt.sum`), which gives `MDifferentiableAt`; the frame-based expression
  agrees with `y ↦ lapRmAt g y (A y) …` near `x`, so the same holds for the latter
  (`MDifferentiableAt.congr_of_eventuallyEq`).

## A caveat on the smoothness level of the requested statement

`Work.Diff.GE.lapRmAt_diff` is stated with the hypothesis `[IsManifold I ((⊤ : ENat) : WithTop ENat) M]`, and
inside the `ContDiff` scope `⊤ : WithTop ℕ∞` is the level `ω` (the **analytic** level), not `∞`
(the `C^∞` level `((⊤ : ℕ∞) : WithTop ℕ∞)`).  The statement is therefore about analytic manifolds —
it is true and is proved below exactly as requested, but every ingredient of the argument is in
fact available for the (weaker, and workspace-wide) hypothesis `[IsManifold I ∞ M]`.  That version
is recorded first, as `Work.Diff.GE.lapRmAt_diff_smooth`; the requested statement is then an
immediate consequence.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

/-- **Differentiability of the rough Laplacian of the curvature along smooth fields**
(smooth-manifold version).

For a smooth metric `g` on a smooth manifold, a point `x` and globally `C^∞` vector fields
`A B C D`, the function `y ↦ ΔRm(g)(y)(A y, B y, C y, D y)` is `C^∞` (hence differentiable) at
`x`. -/
theorem lapRmAt_diff_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (g : Submission.Diff.SMet I M) (x : M)
      (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.lapRmAt g y (A y) (B y) (C y) (D y)) x := by
  intro g x A B C D hA hB hC hD
  classical
  -- a `g`-orthonormal frame near `x` made of globally smooth fields
  obtain ⟨F, hFsm, hFON⟩ := exists_global_ON_frame_smooth (I := I) (M := M) g x
  -- each summand of the frame trace is `C^∞` at `x`
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
        (fun y : M => cov2RmExt g y (F i y) (F i) A B C D) x := by
    intro i
    exact ((kato_cov2RmExt_field (g := g) hLC x
      (V := F i) (A := A) (B := B) (C := C) (D := D)
      (V' := F i) (A' := A) (B' := B) (C' := C) (D' := D)
      (hFsm i) hA hB hC hD (hFsm i) hA hB hC hD
      rfl rfl rfl rfl rfl).2 (F i) (hFsm i)).contMDiffAt
  have hsum : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => ∑ i, cov2RmExt g y (F i y) (F i) A B C D) x := by
    have h := ContMDiffAt.sum (𝕜 := ℝ) (n := ∞) (I := modelWithCornersSelf ℝ ℝ) (I' := I)
      (t := Finset.univ)
      (f := fun (i : Fin (Module.finrank ℝ E)) (y : M) =>
        cov2RmExt g y (F i y) (F i) A B C D) (fun i _ => hterm i)
    simpa using h
  refine (hsum.mdifferentiableAt (by simp)).congr_of_eventuallyEq ?_
  -- near `x` the frame trace computes `lapRmAt`
  filter_upwards [hFON] with y hON
  rw [lapRmAt_trace (g := g) hLC y (fun i => F i y) hON (A y) (B y) (C y) (D y)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- replace the `Classical.epsilon` extensions of `cov2Rm` by the given smooth fields
  show cov2RmExt g y (F i y) (smoothExt y (F i y)) (smoothExt y (A y)) (smoothExt y (B y))
      (smoothExt y (C y)) (smoothExt y (D y)) = cov2RmExt g y (F i y) (F i) A B C D
  rw [cov2RmExt_bind_V (g := g) hLC y (F i y) (smoothExt_cmdiff y (F i y)) (hFsm i)
        (smoothExt_cmdiff y (A y)) (smoothExt_cmdiff y (B y)) (smoothExt_cmdiff y (C y))
        (smoothExt_cmdiff y (D y)) (smoothExt_apply y (F i y))]
  rw [cov2RmExt_bind_A (g := g) hLC y (F i y) (hFsm i) (smoothExt_cmdiff y (A y)) hA
        (smoothExt_cmdiff y (B y)) (smoothExt_cmdiff y (C y)) (smoothExt_cmdiff y (D y))
        (smoothExt_apply y (A y))]
  rw [cov2RmExt_bind_B (g := g) hLC y (F i y) (hFsm i) hA (smoothExt_cmdiff y (B y)) hB
        (smoothExt_cmdiff y (C y)) (smoothExt_cmdiff y (D y)) (smoothExt_apply y (B y))]
  rw [cov2RmExt_bind_C (g := g) hLC y (F i y) (hFsm i) hA hB (smoothExt_cmdiff y (C y)) hC
        (smoothExt_cmdiff y (D y)) (smoothExt_apply y (C y))]
  rw [cov2RmExt_bind_D (g := g) hLC y (F i y) (hFsm i) hA hB hC (smoothExt_cmdiff y (D y)) hD
        (smoothExt_apply y (D y))]

/-- **The requested statement**, with the hypothesis `[IsManifold I ((⊤ : ENat) : WithTop ENat) M]` exactly as
asked for.  Note that in the `ContDiff` scope `⊤ : WithTop ℕ∞` is the analytic level `ω`, so this is
the analytic-manifold case; analyticity is stronger than smoothness, and the smooth case is
`Work.Diff.GE.lapRmAt_diff_smooth` above. -/
theorem lapRmAt_diff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (g : Submission.Diff.SMet I M) (x : M)
      (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.lapRmAt g y (A y) (B y) (C y) (D y)) x := by
  exact lapRmAt_diff_smooth hLC

end Work.Diff.GE
