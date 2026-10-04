import Mathlib
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Additivity of `jetAll` in the packed operator: finite sums

`Work.Diff.EXT.jetAll g j K S` is the `j`-fold iterated covariant derivative of a packed
field-level operator `S : (Fin K → TField) → M → ℝ`, defined as the iterate of the generic Leibniz
step `Work.Diff.EXT.extStep`.  The companion module `Submission/Work/Diff/EXT/jetSmoothDefs.lean`
proves the **subtraction** rule

`jetAll g j K (S - S') F =ᶠ[𝓝 x] jetAll g j K S F - jetAll g j K S' F`

under the hypothesis `JetSmoothOp` on both `S` and `S'` (all the jets of an operator are
mdifferentiable near `x`), i.e. under the condition that the "junk" values `0` of Mathlib's
`mfderiv` on the non-differentiable locus do not destroy the linearity.

This module proves the corresponding statement for a **finite sum** of packed operators,

`jetAll g j K (∑ i, S i) F =ᶠ[𝓝 x] fun y => ∑ i, jetAll g j K (S i) F y`,

again under `JetSmoothOp` for each summand.  This is the form in which linearity in the operator is
used when an operator is *assembled* from finitely many pieces: as soon as each piece has
mdifferentiable jets, so does the sum, and the jets of the sum are the sums of the jets.

## The proof

The induction on the jet order `j` is the same shape as in the subtraction case:

* `j = 0`: pointwise, `(∑ i, S i) F y = ∑ i, (S i) F y`;
* `j = l + 1`: `jetAll g (l+1) K T F = extStep g (jetAll g l K T) F`, and

  - the *germ congruence* `Work.Diff.EXT.extStep_congr_at` allows one to replace the operator
    `jetAll g l K T` by `fun G y => ∑ i, jetAll g l K (S i) G y` on the tuples occurring in the
    recursion (the induction hypothesis gives the congruence on those tuples, which are smooth);
  - at each point `y` near `x` the step `extStep` is *additive* in the operator
    (`Work.Diff.EXT.evolX.extStep_sum_apply`), because the `mvfderiv` term is additive over a finite
    sum of mdifferentiable functions (`Work.Diff.EXT.evolX.mvfderiv_sum_at_apply`) and the Leibniz
    corrections are additive term by term.

The two auxiliary lemmas about `extStep`/`mvfderiv` are stated and proved here; the main theorem is
the finite-sum counterpart of `Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`.
-/

set_option linter.unusedSectionVars false
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

/-- **`mvfderiv` is additive over a finite sum** of functions mdifferentiable at the base point
(evaluated form).  Mathlib's `mfderiv` is `0` on the non-differentiable locus, so the hypothesis
that *each* summand is mdifferentiable at `x` is needed; this is exactly what `JetSmoothOp`
supplies for the jets of the summands. -/
theorem mvfderiv_sum_at_apply {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (x : M)
    (v : TangentSpace I x) (h : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i, f i y) x v = ∑ i, mvfderiv I (f i) x v := by
  classical
  have hdiff : ∀ t : Finset ι, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => ∑ i ∈ t, f i y) x := by
    intro t
    refine (MDifferentiableAt.sum (t := t) (f := f) (fun i _ => h i)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Finset.sum_apply]
  have key : ∀ s : Finset ι,
      mvfderiv I (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = (fun _ : M => (0 : ℝ)) from by
        funext y; simp]
      rw [mvfderiv_const]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [show (fun y : M => ∑ i ∈ insert a s, f i y)
          = ((f a) + (fun y : M => ∑ i ∈ s, f i y)) from by
            funext y; rw [Finset.sum_insert ha]; rfl]
      rw [mvfderiv_add (h a) (hdiff s), add_apply, ih]
  simpa using key Finset.univ

/-- **Pointwise additivity of `extStep` in the packed operator over a finite sum.**  If every
summand's value on the tail tuple is mdifferentiable at `x`, then the Leibniz step of the sum is the
sum of the Leibniz steps.  The `mvfderiv` term is handled by `mvfderiv_sum_at_apply` and the
correction terms by `Finset.sum_sub_distrib`/`Finset.sum_comm`. -/
theorem extStep_sum_apply (g : Submission.Diff.SMet I M) {K : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (F : Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M)) (x : M)
    (hA : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) ((A i) (fun j : Fin K => F j.succ)) x) :
    Work.Diff.EXT.extStep (I := I) (M := M) g (fun G y => ∑ i, A i G y) F x
      = ∑ i, Work.Diff.EXT.extStep (I := I) (M := M) g (A i) F x := by
  classical
  simp only [Work.Diff.EXT.extStep]
  rw [mvfderiv_sum_at_apply (I := I) (fun i => A i (fun j : Fin K => F j.succ)) x (F 0 x)
        (fun i => hA i)]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]

end Helpers

/-- **`jetAll` is additive in the packed operator over a finite sum.**  If every summand `S i` has
mdifferentiable jets near `x` (`JetSmoothOp`), then so does the sum, and the `j`-th jet of the sum
is the sum of the `j`-th jets — i.e. `jetAll g j K` is linear in the packed operator on `JetSmoothOp`
operators.

The proof is the induction on the jet order `j`, exactly as for the subtraction rule
`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`: at the step the operator `jetAll g l K (∑ i, S i)` is
replaced by `fun G y => ∑ i, jetAll g l K (S i) G y` in the germ at `x`
(`Work.Diff.EXT.extStep_congr_at`, fed by the induction hypothesis on the smooth tuples occurring in
the recursion), and then `extStep` is unfolded additively at each point of the neighbourhood
(`Work.Diff.EXT.evolX.extStep_sum_apply`, whose mdifferentiability input comes from the `JetSmoothOp`
hypotheses of the summands). -/
theorem jetAll_sum_of_JetSmoothOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {g : Submission.Diff.SMet I M} {K : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) (x : M)
    (hS : ∀ i, Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g K (S i) x)
    (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (F r)) :
    Work.Diff.EXT.jetAll g j K (∑ i, S i) F =ᶠ[nhds x]
      fun y => ∑ i, Work.Diff.EXT.jetAll g j K (S i) F y := by
  classical
  have key : ∀ (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (F r)) →
      Work.Diff.EXT.jetAll g j K (∑ i, S i) F =ᶠ[𝓝 x]
        (fun y => ∑ i, Work.Diff.EXT.jetAll g j K (S i) F y) := by
    intro j
    induction j with
    | zero =>
        intro F hF
        filter_upwards with z
        simp only [Work.Diff.EXT.jetAll, Finset.sum_apply]
    | succ l ih =>
        intro F hF
        have htail : ∀ i : Fin (K + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
            ((fun i : Fin (K + l) => F i.succ) i) := fun i => hF i.succ
        have hW : ∀ s : Fin (K + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
            (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)) :=
          fun s => Work.Diff.EXT.dirF_smooth hLC g (htail s) (hF 0)
        have h1 : Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (∑ i, S i)) F
            =ᶠ[𝓝 x] Work.Diff.EXT.extStep g
              (fun G y => ∑ i, Work.Diff.EXT.jetAll g l K (S i) G y) F :=
          Work.Diff.EXT.extStep_congr_at (I := I) (M := M) g
            (Work.Diff.EXT.jetAll g l K (∑ i, S i))
            (fun G y => ∑ i, Work.Diff.EXT.jetAll g l K (S i) G y) F x
            (ih (fun i : Fin (K + l) => F i.succ) htail)
            (fun s => ih (Function.update (fun i : Fin (K + l) => F i.succ) s
                (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)))
              (Work.Diff.EXT.smoothF_update' htail s (hW s)))
        have h2 : Work.Diff.EXT.extStep g
              (fun G y => ∑ i, Work.Diff.EXT.jetAll g l K (S i) G y) F
            =ᶠ[𝓝 x] (fun z : M => ∑ i,
              Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (S i)) F z) := by
          filter_upwards [Filter.eventually_all.mpr hS] with y hy
          exact extStep_sum_apply (I := I) (M := M) g
            (fun i => Work.Diff.EXT.jetAll g l K (S i)) F y
            (fun i => hy i l (fun j : Fin (K + l) => F j.succ) htail)
        have e1 : Work.Diff.EXT.jetAll g (l + 1) K (∑ i, S i) F
            = Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (∑ i, S i)) F := by
          simp only [Work.Diff.EXT.jetAll]
        have e2 : (fun z : M => ∑ i, Work.Diff.EXT.jetAll g (l + 1) K (S i) F z)
            = fun z : M => ∑ i,
              Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l K (S i)) F z := by
          funext z
          simp only [Work.Diff.EXT.jetAll]
        rw [e1, e2]
        exact h1.trans h2
  exact key j F hF

end Work.Diff.EXT.evolX
