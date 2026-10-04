import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TermCalc
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ConnCov.RicFlip.SlotAddP_comp
import Submission.Work.Diff.EXT.ConnCov.RicFlip.atomEval_smE
import Submission.Work.Diff.EXT.ConnCov.RicFlip.insAtomAdd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `SmP`/`SlotAddP` invariants of the term calculus

The flip induction `Work.Diff.EXT.ConnCov.RicFlip.honestTowerBoundUniform` carries the term calculus
`Work.Diff.EXT.ConnCov.RicFlip.Term` applied to the base `ric2 (G t)`.  Its two structural inputs
(exported there as `hsmT` and `hslot`) are, for every term `Tm`,

* `AM B.SmP (evalT G t (ric2 (G t)) Tm)` — the object is smooth on smooth tuples, and
* `AMB.SlotAddP (evalT G t (ric2 (G t)) Tm)` — the object is additive in every slot on smooth fields
  (which is what makes the two-connection flip `pD_0 = pD_t + Ins δ` applicable).

Both are proved here by induction on the term:

* the leaves are `RicT (G t) i = pDiter2 (lcOf (G t)) (ric2 (G t)) i`, whose two invariants are
  `Work.Diff.EXT.ConnCov.RicFlip.RicT_good` (proved from `ricAt`-bilinearity and the two
  preservation lemmas of `AMB.pD`);
* the composition node is `Work.Diff.EXT.ConnCov.RicFlip.SlotAddP_comp`, which propagates slot
  additivity through a one-atom substitution using the smoothness of the atom
  (`atomEval_smE`) and its additivity (`insAtomAdd`); the same substitution story gives the
  smoothness invariant (`osubEval_smE` below).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **Smoothness of a one-atom substitution on smooth tuples.** -/
theorem osubEval_smE (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a b ord : ℕ} (Φ : O.OSub a b ord)
    {F : Fin a → AMB.TF (I := I) (M := M)}
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) (i : Fin b) :
    Work.Diff.EXT.ATower.SmE I M (Φ.eval G t F i) := by
  by_cases h : i = Φ.idx
  · rw [h, O.OSub.eval_atom Φ F]
    exact atomEval_smE hLC G t Φ.τ F hF
  · rw [O.OSub.eval_slot Φ F h]
    exact hF _

/-- **Slot additivity of every term of the calculus** (the `hslot` invariant of the flip
induction). -/
theorem slotAddP_evalT (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ {n : ℕ} (Tm : Term n),
      AMB.SlotAddP (I := I) (M := M) (evalT G t (ric2 (G t)) Tm) := by
  intro n Tm
  induction Tm with
  | leaf i =>
      show AMB.SlotAddP (I := I) (M := M)
        (pDiter2 (Submission.Diff.lcOf (G t)) (ric2 (G t)) i)
      exact (RicT_good hLC (G t) i).1
  | comp Ψ T ih =>
      exact SlotAddP_comp (I := I) (M := M) G t Ψ ih
        (fun F hF => atomEval_smE hLC G t Ψ.τ F hF)
        (fun j v W W' hv hW hW' => insAtomAdd hLC G t _ j v W W' hv hW hW')

/-- **Smoothness of every term of the calculus on smooth tuples** (the `hsmT` invariant). -/
theorem smP_evalT (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ {n : ℕ} (Tm : Term n),
      AMB.SmP (I := I) (M := M) (evalT G t (ric2 (G t)) Tm) := by
  intro n Tm
  induction Tm with
  | leaf i =>
      show AMB.SmP (I := I) (M := M)
        (pDiter2 (Submission.Diff.lcOf (G t)) (ric2 (G t)) i)
      exact (RicT_good hLC (G t) i).2
  | comp Ψ T ih =>
      intro F hF
      exact ih _ (fun i => osubEval_smE hLC G t Ψ hF i)

end Work.Diff.EXT.ConnCov.RicFlip
