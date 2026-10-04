import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.NoCKit
import Submission.Work.Diff.EXT.ConnCov.pD_Ins

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-connection flip of a *slot-additive* object, and its term expansion kit

## The finding recorded here (important for the whole `ConnCov` chapter)

The `step`-recursion `Work.Diff.EXT.ATower.step (≡ AMB.pD)` of the *modified* tower of `baseRic`
(`baseRic g v A B C = Ric(A,B)`, the third slot a dummy) produces an object which is **not additive
in its direction slots**.  Explicitly, at level `1`,

`AMB.pD cov (pack (baseRic g)) F x = ∇_{F 0} Ric(F 1, F 2) - Ric(F 1, F 2)`,

whose dependence on the direction field `F 0` is **affine** and not linear (`F 0 = 0` gives
`-Ric(F1,F2) ≠ 0`).  Consequently every flip identity of the shape

`pD (lcOf (G 0)) X = pD (lcOf (G t)) X + Ins δ X`

— in particular `FlipKit.step_flip_NoC2`, whose hypothesis is additivity in the direction slots and
in the `A`, `B` slots — **cannot** be applied to the intermediate objects of the word expansion of
`pD_0^k`; the "word expansion" of `RicFlip/Defs.lean` / `ricTowerFlipBound` therefore does not go
through as stated.  The available correct routes are:

* (this file) use the **honest** tower, i.e. the tower of `Ric` as a `(0,2)`-tensor
  (`RicT g i = pDiter (lcOf g) (ric2 g) i : Fam (i+2)`, no dummy slot).  *That* object **is** slot
  additive, and then the flip below applies verbatim with the full insertion `AMB.Ins`; the
  conversion between the honest tower and the modified tower `tower (lcOf g) (baseRic g) ·` is the
  *shift identity* (`tower_eq_htower_expansion`, smooth fields), a purely combinatorial statement.
* or carry an affine/linear classification of the slots (much more bookkeeping).

## Contents of this file

* `deltaTens` — the connection difference `covDiff G t` as an `AMB.Tens12`;
* `pD_flip_full` — the flip identity for slot-additive objects;
* `Ins_deltaTens_eq_sum` — the insertion as a sum of the one-atom substitutions `O.insSub j`
  (`j : Fin N` runs over *all* slots here: no slot is exempted), the form consumed by the
  substitution calculus of `RicFlip/OSubKit.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The connection difference `covDiff G t = ∇^{G t} − ∇^{G 0}`, as a `(1,2)`-tensor for the
insertion operators. -/
noncomputable def deltaTens (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    AMB.Tens12 (I := I) (M := M) :=
  fun X Y => Work.Diff.EXT.ConnCov.covDiff G t X Y

/-- **The flip identity for a slot-additive object.**  If `τ` is additive in every slot (on smooth
fields), then one packed recursion step with the fixed connection `∇^{G 0}` differs from one packed
recursion step with the moving connection `∇^{G t}` by exactly the insertion of the connection
difference. -/
theorem pD_flip_full (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) {N : ℕ} {τ : Fam (I := I) (M := M) N} (hadd : AMB.SlotAddP τ)
    (F : Fin (N + 1) → TF (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.ATower.SmE I M (F i)) :
    AMB.pD (Submission.Diff.lcOf (G 0)) τ F
      = AMB.pD (Submission.Diff.lcOf (G t)) τ F + AMB.Ins (deltaTens G t) τ F := by
  have hstep : ∀ (g : SMet I M), AMB.pD (lcOf g) τ F
      = fun x => mvfderiv I (τ (fun i : Fin N => F i.succ)) x (F 0 x)
          - ∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf g (F i.succ) y (F 0 y))) x := fun g => rfl
  have hfield : ∀ i : Fin N, (fun y : M => lcOf (G t) (F i.succ) y (F 0 y))
      = (fun y : M => lcOf (G 0) (F i.succ) y (F 0 y))
        + (fun y : M => deltaTens G t (F i.succ) (F 0) y) := by
    intro i
    funext y
    simp only [deltaTens, Work.Diff.EXT.ConnCov.covDiff, Pi.add_apply, Pi.sub_apply]
    abel
  have hlc : ∀ (g : SMet I M) (Y Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => lcOf g Y y (Z y)) :=
    fun g Y Z hY hZ => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g Y Z hY hZ
  have hδsm : ∀ (Y Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => deltaTens G t Y Z y) :=
    fun Y Z hY hZ => (hlc (G t) Y Z hY hZ).sub_section (hlc (G 0) Y Z hY hZ)
  rw [hstep (G 0), hstep (G t)]
  funext x
  have hsum : (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
        (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x)
      = (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x)
        + (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => deltaTens G t (F i.succ) (F 0) y)) x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfield i]
    exact hadd i (fun k : Fin N => F k.succ) (fun y => lcOf (G 0) (F i.succ) y (F 0 y))
      (fun y => deltaTens G t (F i.succ) (F 0) y) (fun k => hF _)
      (hlc (G 0) _ _ (hF _) (hF 0)) (hδsm _ _ (hF _) (hF 0)) x
  simp only [Pi.add_apply]
  rw [hsum, Ins]
  ring

/-- **The insertion as a sum of one-atom substitutions.**  Here the sum runs over *all* slots
`j : Fin N` (nothing is exempted), and each term is the evaluation of `τ` at the tuple in which slot
`j` has been replaced by the connection difference with the direction `F 0`. -/
theorem Ins_deltaTens_eq_sum (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {N : ℕ}
    (τ : Fam (I := I) (M := M) N) (F : Fin (N + 1) → TF (I := I) (M := M)) (x : M) :
    AMB.Ins (deltaTens G t) τ F x
      = ∑ j : Fin N, τ ((insSub N j).eval G t F) x := by
  rw [Ins]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [insSub_eval]
  rfl

end Work.Diff.EXT.ConnCov.RicFlip
