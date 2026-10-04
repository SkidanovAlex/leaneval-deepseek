import Mathlib
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.ladderEfDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of all the jets of the rough Laplacian operator `lapOpE`

`Work.Diff.EXT.JetSmoothOp g K S x` is the condition under which `jetAll` is *linear* in a packed
operator `S` (`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`): for every jet order `l` and every tuple
`F` of smooth fields, the function `y ↦ jetAll g l K S F y` is mdifferentiable near `x`.  This
module discharges the condition for the rough-Laplacian operator

`lapOpE Ef g k F = ∑_m ckt g (k+2) (Ef m, Ef m, F)`

of `Submission/Work/Diff/EXT/ladderSrcDefs.lean`, traced in a frame *field* `Ef` which is smooth
everywhere (hypothesis `hEf`).

## The proof

The point is that `jetAll` is a recursion whose *step* is built from two operations that preserve
`C^∞`:

* `mvfderiv I Φ · (F 0 ·)` for `Φ` a `C^∞` function and `F 0` a smooth field
  (`Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff`), and
* the Leibniz corrections `dirF g X v = ∇_X v`, which are smooth in the direction slots
  (`Work.Diff.EXT.dirF_smooth`, from the *proved* contract `LCSmooth`: here
  `Work.EXT.lcSmooth_noBoundary` supplies `LCSmooth I M` with no boundary hypothesis, since
  `SMet I M` is a *smooth* metric bundle).

Consequently, **if the operator itself maps smooth tuples to `C^∞` functions, then so do all its
jets**, and `JetSmoothOp` follows at once.  This is `extStep_contMDiff` (the step) and
`jetAll_contMDiff_of_base` (the induction), stated for an arbitrary packed operator; the concrete
input for the rough Laplacian is smoothness of the tower `ckt` on smooth tuples
(`Work.Diff.EXT.tensProp_all`, in `curvNormK_frame_indep.lean`).

Nothing here uses that `lapOpE` is a Laplacian: the same two lemmas discharge `JetSmoothOp` for
any operator built from `ckt` in smooth fields.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **The step of the recursion preserves `C^∞`.**  If a packed operator `A` of arity `K` maps
every tuple of smooth fields to a `C^∞` function, then so does its covariant-derivative step
`extStep g A` (of arity `K + 1`): the two ingredients of `extStep` are the derivative
`y ↦ (∇(A (F ∘ succ)))(y)(F 0 y)` of a `C^∞` function along a smooth field, and the Leibniz
corrections `A (update (F ∘ succ) s (∇_{slot s} (F 0)))`, which are `C^∞` because `∇_{X} v` is
smooth in `X, v` (`dirF_smooth`, from `LCSmooth`). -/
theorem extStep_contMDiff (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {K : ℕ}
    (A : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (hA : ∀ F, (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) → CMDiff ∞ (A F)) :
    ∀ F : Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      CMDiff ∞ (Work.Diff.EXT.extStep (I := I) (M := M) g A F) := by
  intro F hF
  have htail : ∀ i : Fin K, Work.Diff.EXT.SmoothF (I := I) (M := M) ((fun i : Fin K => F i.succ) i) :=
    fun i => hF i.succ
  have hder : CMDiff ∞ (fun y : M => (mvfderiv I (A (fun i : Fin K => F i.succ)) y) (F 0 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (f := A (fun i : Fin K => F i.succ))
      (X := F 0) (hA _ htail) (hF 0)
  have hsum : CMDiff ∞ (fun y : M => ∑ s : Fin K, A (Function.update (fun i : Fin K => F i.succ) s
      (Work.Diff.EXT.dirF g ((fun i : Fin K => F i.succ) s) (F 0))) y) :=
    ContMDiff.sum (t := Finset.univ) (f := fun s : Fin K => A (Function.update (fun i : Fin K => F i.succ) s
      (Work.Diff.EXT.dirF g ((fun i : Fin K => F i.succ) s) (F 0)))) (fun s _ => hA _
        (Work.Diff.EXT.smoothF_update' htail s (Work.Diff.EXT.dirF_smooth hLC g (htail s) (hF 0))))
  exact hder.sub hsum

/-- **All the jets of a packed operator are `C^∞`, if its level `0` is.**  The induction on the jet
order `l`: the level `l + 1` is `extStep g (jetAll g l K S)`, and `extStep_contMDiff` propagates
`C^∞` from level `l` (available at all tuples by the induction hypothesis) to level `l + 1`. -/
theorem jetAll_contMDiff_of_base (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {K : ℕ}
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (h0 : ∀ F, (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) → CMDiff ∞ (S F)) :
    ∀ (l : ℕ) (F : Fin (K + l) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      CMDiff ∞ (fun y : M => Work.Diff.EXT.jetAll (I := I) (M := M) g l K S F y) := by
  intro l
  induction l with
  | zero => intro F hF; exact h0 F hF
  | succ l ih =>
      intro F hF
      exact extStep_contMDiff hLC g (K := K + l)
        (A := fun (F' : Fin (K + l) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          Work.Diff.EXT.jetAll (I := I) (M := M) g l K S F' y)
        (fun F' hF' => ih F' hF') F hF

end Helpers

/-- **`JetSmoothOp` for the rough Laplacian traced in a smooth frame field.**  The level-`0`
operator `F ↦ ∑_m ckt g (k+2) (Ef m, Ef m, F)` is `C^∞` on smooth tuples because the tower `ckt`
is (`Work.Diff.EXT.tensProp_all`), so all its jets are (`jetAll_contMDiff_of_base`), which is
exactly `JetSmoothOp`. -/
theorem opJetSmooth_lapOpE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (k : ℕ)
    (g : Submission.Diff.SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Ef i)) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (k + 4)
      (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g k) x := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hbase : ∀ F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      CMDiff ∞ (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g k F) := by
    intro F hF
    show CMDiff ∞ (fun y : M => ∑ m : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.ckt (I := I) (M := M) g (k + 2)
        (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y)
    refine ContMDiff.sum (t := Finset.univ) (f := fun m : Fin (Module.finrank ℝ E) =>
      Work.Diff.EXT.ckt (I := I) (M := M) g (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F))) ?_
    intro m _
    exact (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g (k + 2) _
      (Work.Diff.EXT.smoothF_cons (I := I) (M := M) (hEf m)
        (Work.Diff.EXT.smoothF_cons (I := I) (M := M) (hEf m) hF))).1
  have hj := jetAll_contMDiff_of_base (I := I) (M := M) hLC g
    (S := Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g k) hbase
  filter_upwards with y
  intro l F hF
  exact (hj l F hF).contMDiffAt.mdifferentiableAt (by simp)

end Work.Diff.EXT.evolX
