import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `htower (lcOf g) (baseRic g) = lift23 (tower2 (lcOf g) (baseRic2 g))`

`Work.Diff.EXT.ConnCov.baseRic g` ignores its third value slot (`CIndep`), so the recursion `hstep`
(the honest `step`, `step + drop`) that defines `htower` agrees with the recursion `step2` of the
honest `(0,2)`-tower `tower2` with the dummy third slot:

`htower (lcOf g) (baseRic g) k v A B C x = tower2 (lcOf g) (baseRic2 g) k v A B x`.

This is the `hbridge` input of `Work.Diff.EXT.ConnCov.moving_honest_ric_tower_aux`.

(Kept in its own module — it is the only declaration of the `RicTowerDefs` chain that
`Submission/Work/Diff/EXT/ConnCov/ricTowerBound_fixed.lean` needs, and that file has to avoid the
`RicTowerDefs`/`deltaTower` duplicate declarations.)
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem htower_lift23_tower2 (g : SMet I M) :
    ∀ (j : ℕ) (v : Fin j → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y) (x : M),
      htower (lcOf g) (baseRic g) j v A B C x = tower2 (lcOf g) (baseRic2 g) j v A B x := by
  intro j
  induction j with
  | zero => intro v A B C x; rfl
  | succ j ih =>
      intro v A B C x
      have hτ : CIndep (htower (lcOf g) (baseRic g) j) :=
        cIndep_htower (lcOf g) (cIndep_baseRic g) j
      have hmv : mvfderiv I (htower (lcOf g) (baseRic g) j (fun i : Fin j => v i.succ) A B C)
            x (v 0 x)
          = mvfderiv I (tower2 (lcOf g) (baseRic2 g) j (fun i : Fin j => v i.succ) A B)
              x (v 0 x) :=
        congrArg (fun F : M → ℝ => mvfderiv I F x (v 0 x))
          (funext fun y => ih _ A B C y)
      rw [htower_succ, hstep_apply (lcOf g) hτ, tower2_succ, step2_apply, hmv]
      simp only [ih]

end Work.Diff.EXT.ConnCov
