import Mathlib
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Locality of the packed jets in the operator, for tuples of smooth fields

If two packed operators of arity `K` agree *pointwise* (at every base point, for every tuple of
smooth fields), then so do all their packed jets:

`jetAll g j K S F = jetAll g j K S' F` for every tuple `F` of smooth fields.

This is the form in which locality is used when the two operators agree only after an identification
of their slots (e.g. `Work.Diff.EXT.evolX.connVarOp` versus the sum of the contracted towers
`Work.Diff.EXT.evolX.substOp`, whose inserted field is a `smoothExt`-extension of the same value).

The proof is the induction on the jet order: `jetAll` is the iteration of `extStep`, whose two
ingredients are the `mvfderiv` of `S (F ∘ succ)` along `F 0` and the Leibniz corrections
`S (update (F ∘ succ) i (dirF g ((F ∘ succ) i) (F 0)))`; the induction hypothesis, applied at the
relevant tuples (which are smooth because `dirF` of smooth fields is smooth), identifies the two
operators' values pointwise.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem jetAll_congr_of_pointwise [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    {g : Submission.Diff.SMet I M} {K : ℕ}
    {S S' : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ}
    (h : ∀ F, (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      ∀ y, S F y = S' F y) :
    ∀ (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      ∀ y, Work.Diff.EXT.jetAll g j K S F y = Work.Diff.EXT.jetAll g j K S' F y := by
  intro j
  induction j with
  | zero => intro F hF y; exact h F hF y
  | succ l ih =>
    intro F hF y
    have htail : ∀ i : Fin (K + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
        ((fun i : Fin (K + l) => F i.succ) i) := fun i => hF i.succ
    simp only [Work.Diff.EXT.jetAll]
    simp only [Work.Diff.EXT.extStep, Finset.sum_apply]
    -- the differentiated operators agree
    have hfun : (fun y' : M => Work.Diff.EXT.jetAll g l K S
          (fun i : Fin (K + l) => F i.succ) y')
        = fun y' : M => Work.Diff.EXT.jetAll g l K S'
          (fun i : Fin (K + l) => F i.succ) y' := by
      funext y'
      exact ih (fun i : Fin (K + l) => F i.succ) htail y'
    -- the Leibniz corrections agree
    have hcorr : ∀ i : Fin (K + l),
        Work.Diff.EXT.jetAll g l K S
            (Function.update (fun i : Fin (K + l) => F i.succ) i
              (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) i) (F 0))) y
          = Work.Diff.EXT.jetAll g l K S'
            (Function.update (fun i : Fin (K + l) => F i.succ) i
              (Work.Diff.EXT.dirF g ((fun i : Fin (K + l) => F i.succ) i) (F 0))) y :=
      fun i => ih _ (Work.Diff.EXT.smoothF_update htail
        (Work.Diff.EXT.dirF_smooth hLC g (htail i) (hF 0))) y
    rw [show (mvfderiv I (fun y' : M => Work.Diff.EXT.jetAll g l K S
          (fun i : Fin (K + l) => F i.succ) y') y) (F 0 y)
        = (mvfderiv I (fun y' : M => Work.Diff.EXT.jetAll g l K S'
          (fun i : Fin (K + l) => F i.succ) y') y) (F 0 y) from by rw [hfun]]
    rw [Finset.sum_congr rfl (fun i _ => hcorr i)]

end Work.Diff.EXT.evolX
