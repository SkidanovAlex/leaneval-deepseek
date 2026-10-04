import Mathlib
import Submission.Work.Diff.EXT.evolKDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The classical reaction-shaped goal of the `k`-th order Shi estimate (minimal module)

This module exists for one structural reason: the *predicate* `Work.Diff.EXT.EvolCompKFixReact`
(the sharp, classical-reaction-shaped evolution estimate for `∇^k Rm`) was originally defined inside
`Submission/Work/Diff/EXT/evolCompKFix_all.lean`, and the *ladder* development
(`Submission/Work/Diff/EXT/{reactDefs,towerReactDefs,ladderEfDefs,ladderEfDToReact}.lean`,
`Submission/Work/Diff/EXT/evolX/*`) needs the predicate as the *conclusion* of its conversion
theorem `Work.Diff.EXT.ladderEfDToReact`.  Since those modules imported `evolCompKFix_all.lean`, and
`evolCompKFix_all.lean` must in turn *use* `ladderEfDToReact` to finish the `k ≥ 2` case of
`Work.Diff.EXT.evolCompKFix_all`, the two sides were in a circular-import deadlock.

Fix: the predicate lives *here*, in a module that imports only `evolKDefs` (the frozen vocabulary
`covKRm`, `lapCovKRm`, `curvNormK`, `IsRicciFlow`).  Both `evolCompKFix_all.lean` and the ladder
modules can import this file, and `evolCompKFix_all.lean` re-exports it, so nothing that imports the
former breaks.  The ladder modules should replace their `import
Submission.Work.Diff.EXT.evolCompKFix_all` by an import of this module (plus, if they need them,
their own local copies of the two `covKRm`-bridges listed at the top of `evolCompKFixReact_all.lean`).
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The classical reaction-shaped estimate for `∇^k Rm`.**  This is the invariant that the
induction `k → k+1` on the explicit reaction has to produce: the derivative of the fixed-vector
component is the rough Laplacian plus a reaction whose bound is the *classical reaction shape*
`Σ_{i+j=k} √(f_i) √(f_j)` times the metric norms of the `k+4` arguments (`f_j = curvNormK (G t) x j`
is `|∇^j Rm|²`).  It is *sharper* than `EvolCompKFix k`: `Work.Diff.EXT.sum_sqrt_le` (in
`evolCompKFix_all.lean`) converts it into the bound of `EvolCompKFix k`. -/
def EvolCompKFixReact (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x),
        ∃ D : ℝ,
          HasDerivWithinAt (fun s => covKRm (G s) x k u a b c d) D (Set.Ico 0 T) t ∧
          D ≤ lapCovKRm (G t) x k u a b c d
              + C * (∑ i ∈ Finset.range (k + 1), Real.sqrt (curvNormK (G t) x i)
                        * Real.sqrt (curvNormK (G t) x (k - i)))
                  * ((∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r)))
                      * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                      * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d))

end Work.Diff.EXT
