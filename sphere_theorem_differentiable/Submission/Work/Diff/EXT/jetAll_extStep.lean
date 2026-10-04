import Mathlib
import Submission.Work.Diff.EXT.reactDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The ladder step of `jetAll`** (auxiliary form of `Work.Diff.EXT.jetAll_extStep`).

One `extStep` may be moved from the jet order of `jetAll` into the arity of the packed operator:
the two tuples are identified by the `Fin.cast` reindexing `Fin (K + (j+1)) → Fin ((K+1) + j)`.

The proof is the induction on the jet order `j`.  The step is the *bookkeeping* of the recursion:
both sides unfold to `extStep`, the inner operator of the left-hand side is `jetAll g (l+1) K S` and
the operator of the right-hand side is `jetAll g l (K+1) (extStep g S)` — the inductive hypothesis
gives that the second is the first composed with the reindexing `Fin.cast hc` — and one checks that

* `Fin.cast hFc (i.succ) = (Fin.cast hc i).succ` (`Fin.cast_succ_eq`), i.e. `Fin.cast` commutes with
  `Fin.succ`, so the reindexed *tails* of the two tuples agree;
* `Fin.cast hFc 0 = 0`, so the two *heads* (the new derivative direction, and the vector on which the
  inner derivative is evaluated) agree;
* `Fin.cast hc` is injective, so it commutes with `Function.update`, which is what lets the
  Leibniz-correction sums be matched term by term (and then reindexed by
  `Fintype.sum_bijective`).

Here `j` is quantified *first* so that the induction hypothesis is available at every base point
`y` (the step differentiates the two operators in space, so the inductive hypothesis is needed as a
statement about all `y`, not only about `x`). -/
private theorem jetAll_extStep_aux (g : SMet I M) :
    ∀ (j K : ℕ) (S : (Fin K → TField (I := I) (M := M)) → M → ℝ)
      (F : Fin ((K + 1) + j) → TField (I := I) (M := M)) (x : M),
      jetAll g (j + 1) K S
          (fun r => F (Fin.cast (by omega : K + (j + 1) = (K + 1) + j) r)) x
        = jetAll g j (K + 1) (extStep (I := I) (M := M) g S) F x := by
  intro j
  induction j with
  | zero =>
    intro K S F x
    change extStep g S
        (fun r : Fin (K + (0 + 1)) =>
          F (Fin.cast (by omega : K + (0 + 1) = (K + 1) + 0) r)) x
      = extStep g S F x
    congr 1
  | succ l ih =>
    intro K S F x
    have hc : K + (l + 1) = (K + 1) + l := by omega
    have hFc : K + (l + 1 + 1) = (K + 1) + (l + 1) := by omega
    change extStep g (jetAll g (l + 1) K S)
        (fun r : Fin (K + (l + 1 + 1)) => F (Fin.cast hFc r)) x
      = extStep g (jetAll g l (K + 1) (extStep g S)) F x
    -- the inductive hypothesis, in the form used below
    have hAB : ∀ (G : Fin ((K + 1) + l) → TField (I := I) (M := M)) (y : M),
        jetAll g (l + 1) K S (fun i => G (Fin.cast hc i)) y
          = jetAll g l (K + 1) (extStep g S) G y := fun G y => ih K S G y
    simp only [extStep]
    -- `Fin.cast` commutes with `Fin.succ`: the two tails of the tuples agree after reindexing
    have htail_pt : ∀ i : Fin (K + (l + 1)),
        F (Fin.cast hFc i.succ) = F ((Fin.cast hc i).succ) := by
      intro i
      apply congrArg F
      ext
      simp [Fin.val_cast, Fin.val_succ]
    -- the two heads agree
    have hF0 : F (Fin.cast hFc (0 : Fin (K + (l + 1 + 1)))) = F (0 : Fin (K + 1 + (l + 1))) := by
      simp
    -- normalise the goal: only the reindexing `Fin.cast hc` is left
    simp only [htail_pt, hF0]
    -- the differentiated operators agree
    have hfun : jetAll g (l + 1) K S (fun i => F ((Fin.cast hc i).succ))
        = jetAll g l (K + 1) (extStep g S) (fun i : Fin (K + 1 + l) => F i.succ) := by
      funext y
      exact hAB (fun i : Fin (K + 1 + l) => F i.succ) y
    -- the Leibniz corrections agree, term by term
    have hterm : ∀ s : Fin (K + (l + 1)),
        jetAll g (l + 1) K S
            (Function.update (fun i : Fin (K + (l + 1)) => F ((Fin.cast hc i).succ)) s
              (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x
          = jetAll g l (K + 1) (extStep g S)
              (Function.update (fun i : Fin (K + 1 + l) => F i.succ)
                (Fin.cast hc s) (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x := by
      intro s
      have hUpd : Function.update (fun i : Fin (K + (l + 1)) => F ((Fin.cast hc i).succ)) s
            (dirF g (F ((Fin.cast hc s).succ)) (F 0))
          = (fun i : Fin (K + (l + 1)) =>
              Function.update (fun i : Fin (K + 1 + l) => F i.succ) (Fin.cast hc s)
                (dirF g (F ((Fin.cast hc s).succ)) (F 0)) (Fin.cast hc i)) := by
        funext i
        rw [Function.update_apply, Function.update_apply]
        by_cases hi : i = s
        · subst hi
          simp only [↓reduceIte]
        · have hne : Fin.cast hc i ≠ Fin.cast hc s := by
            intro h
            exact hi (Fin.ext (by simpa [Fin.val_cast] using congrArg Fin.val h))
          simp only [hi, hne, ↓reduceIte]
      rw [hUpd]
      exact hAB (Function.update (fun i : Fin (K + 1 + l) => F i.succ) (Fin.cast hc s)
        (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x
    -- the correction sums agree
    have hsum : (∑ s : Fin (K + (l + 1)),
          jetAll g (l + 1) K S
            (Function.update (fun i : Fin (K + (l + 1)) => F ((Fin.cast hc i).succ)) s
              (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x)
        = ∑ t : Fin (K + 1 + l),
          jetAll g l (K + 1) (extStep g S)
            (Function.update (fun i : Fin (K + 1 + l) => F i.succ) t
              (dirF g (F t.succ) (F 0))) x := by
      calc (∑ s : Fin (K + (l + 1)),
            jetAll g (l + 1) K S
              (Function.update (fun i : Fin (K + (l + 1)) => F ((Fin.cast hc i).succ)) s
                (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x)
          = ∑ s : Fin (K + (l + 1)),
            jetAll g l (K + 1) (extStep g S)
              (Function.update (fun i : Fin (K + 1 + l) => F i.succ) (Fin.cast hc s)
                (dirF g (F ((Fin.cast hc s).succ)) (F 0))) x :=
              Finset.sum_congr rfl (fun s _ => hterm s)
        _ = ∑ t : Fin (K + 1 + l),
            jetAll g l (K + 1) (extStep g S)
              (Function.update (fun i : Fin (K + 1 + l) => F i.succ) t
                (dirF g (F t.succ) (F 0))) x :=
              Fintype.sum_bijective (finCongr hc) (finCongr hc).bijective _ _
                (fun s => by rw [finCongr_apply])
    rw [hfun, hsum]

/-- **The ladder step of `Work.Diff.EXT.jetAll`.**  One covariant derivative may be moved out of
the jet order and into the arity of the packed tensorial operator: the `(j+1)`-st jet of the
arity-`K` operator `S` equals the `j`-th jet of the arity-`(K+1)` operator
`Work.Diff.EXT.extStep g S`, the two tuples being identified by the (`Fin.cast`) reindexing
`Fin (K + (j+1)) → Fin ((K+1) + j)`.

This is the definitional unfolding of `jetAll` (its recursion in the jet order is exactly
`extStep`), together with the `Fin.cast` bookkeeping of the reindexing. -/
theorem jetAll_extStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (j K : ℕ)
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (F : Fin ((K + 1) + j) → Work.Diff.EXT.TField (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.jetAll (I := I) (M := M) g (j + 1) K S
        (fun r => F (Fin.cast (by omega : K + (j + 1) = (K + 1) + j) r)) x
      = Work.Diff.EXT.jetAll (I := I) (M := M) g j (K + 1)
          (Work.Diff.EXT.extStep (I := I) (M := M) g S) F x := by
  exact jetAll_extStep_aux g j K S F x

end Work.Diff.EXT
