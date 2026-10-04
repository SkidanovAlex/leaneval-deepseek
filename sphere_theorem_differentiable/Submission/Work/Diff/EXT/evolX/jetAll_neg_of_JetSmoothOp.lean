import Mathlib
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.jetAll_sum_of_JetSmoothOp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Negation of the packed operator: `jetAll g j K (-S) = - jetAll g j K S`

`Work.Diff.EXT.jetAll` is the `j`-fold iterated covariant derivative of a packed field-level
operator `S : (Fin K → TField) → M → ℝ`, i.e. the iterate of the Leibniz step
`Work.Diff.EXT.extStep`.  The companion modules prove

* `Work.Diff.EXT.jetAll_sub_of_JetSmoothOp` — subtraction in the operator, under `JetSmoothOp`;
* `Work.Diff.EXT.evolX.jetAll_sum_of_JetSmoothOp` — finite sums in the operator, under
  `JetSmoothOp` for each summand.

This module proves the *negation* rule, `jetAll g j K (fun G y ↦ - S G y) F =ᶠ[𝓝 x] - jetAll g j K S F`.

Unlike the subtraction rule this needs **no** mdifferentiability hypothesis: the only place where
linearity can fail is Mathlib's `mfderiv`, which is `0` on the non-differentiable locus, and `-f` is
mdifferentiable at a point exactly when `f` is.  Hence `mvfderiv` is odd *unconditionally*
(`mvfderiv_neg`, used below), and the induction on the jet order goes through with the
`JetSmoothOp` hypothesis of the statement never being used.  (The hypothesis is kept in the
statement for uniformity with the subtraction and sum rules, where it is essential.)

The proof is the induction on the jet order:

* `j = 0`: `jetAll g 0 K (-S) F = (-S) F = - S F` pointwise;
* `j = l + 1`: `jetAll g (l+1) K T F = extStep g (jetAll g l K T) F`, so the two sides are the
  `extStep` of the level-`l` operators `jetAll g l K (-S)` and `- jetAll g l K S`; these agree as
  germs at `x` by the induction hypothesis on the (smooth) tuples occurring in the recursion
  (`Work.Diff.EXT.extStep_congr_at`), and `extStep` is odd in the operator
  (`Work.Diff.EXT.evolX.extStep_neg_apply`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **`mvfderiv` is odd**, in evaluated form.  The statement is *unconditional*: Mathlib's
`mfderiv` is `0` on the non-mdifferentiable locus, and `-f` is mdifferentiable at a point exactly
when `f` is, so even there both sides vanish. -/
theorem mvfderiv_neg_apply_evolX (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => - f y) x v = - mvfderiv I f x v := by
  rw [show (fun y : M => - f y) = -f from rfl, mvfderiv_neg]
  rfl

/-- **`extStep` is odd in the packed operator**, pointwise.  Writing out
`extStep g T F y = (∇_{F 0} (T ∘ succ)) y − ∑_s T (slots with s replaced by ∇_{F 0} slot)`, both
the `mvfderiv` term and the Leibniz corrections are odd, so the whole expression is odd. -/
theorem extStep_neg_apply (g : Submission.Diff.SMet I M) {K : ℕ}
    (T : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (F : Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.extStep (I := I) (M := M) g (fun G y => - T G y) F x
      = - Work.Diff.EXT.extStep (I := I) (M := M) g T F x := by
  simp only [Work.Diff.EXT.extStep, Finset.sum_neg_distrib]
  rw [mvfderiv_neg_apply_evolX]
  ring

end Helpers

theorem jetAll_neg_of_JetSmoothOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {g : Submission.Diff.SMet I M} {K : ℕ}
    {S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ} {x : M}
    (hS : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g K S x)
    (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (F r)) :
    Work.Diff.EXT.jetAll g j K (fun F y => - S F y) F =ᶠ[nhds x]
      fun y => - Work.Diff.EXT.jetAll g j K S F y := by
  have key : ∀ (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (F r)) →
      Work.Diff.EXT.jetAll g j K (fun G y => - S G y) F =ᶠ[𝓝 x]
        (fun y => - Work.Diff.EXT.jetAll g j K S F y) := by
    intro j
    induction j with
    | zero =>
        intro F hF
        filter_upwards with z
        simp only [Work.Diff.EXT.jetAll]
    | succ l ih =>
        intro F hF
        have htail : ∀ i : Fin (K + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
            ((fun i : Fin (K + l) => F i.succ) i) := fun i => hF i.succ
        have hW : ∀ s : Fin (K + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
            (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)) :=
          fun s => Work.Diff.EXT.dirF_smooth hLC g (htail s) (hF 0)
        have h1 : Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (fun G y => - S G y)) F
            =ᶠ[𝓝 x] Work.Diff.EXT.extStep g
              (fun G y => - Work.Diff.EXT.jetAll g l K S G y) F :=
          Work.Diff.EXT.extStep_congr_at (I := I) (M := M) g
            (Work.Diff.EXT.jetAll g l K (fun G y => - S G y))
            (fun G y => - Work.Diff.EXT.jetAll g l K S G y) F x
            (ih (fun i : Fin (K + l) => F i.succ) htail)
            (fun s => ih (Function.update (fun i : Fin (K + l) => F i.succ) s
                (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)))
              (Work.Diff.EXT.smoothF_update' htail s (hW s)))
        have h2 : Work.Diff.EXT.extStep g
              (fun G y => - Work.Diff.EXT.jetAll g l K S G y) F
            =ᶠ[𝓝 x] (fun z : M =>
              - Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K S) F z) := by
          filter_upwards with y
          exact extStep_neg_apply (I := I) (M := M) g
            (Work.Diff.EXT.jetAll g l K S) F y
        have e1 : Work.Diff.EXT.jetAll g (l + 1) K (fun G y => - S G y) F
            = Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (fun G y => - S G y)) F := by
          simp only [Work.Diff.EXT.jetAll]
        have e2 : (fun z : M => - Work.Diff.EXT.jetAll g (l + 1) K S F z)
            = fun z : M =>
              - Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K S) F z := by
          funext z
          simp only [Work.Diff.EXT.jetAll]
        rw [e1, e2]
        exact h1.trans h2
  exact key j F hF

end Work.Diff.EXT.evolX
