import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestFlip
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.pack_bridge

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The *honest* tower of the Ricci tensor, as a packed `Fam (i+2)` object

`Work.Diff.EXT.ATower.tower (lcOf g) (baseRic g) i` is the `i`-th covariant derivative of the
`(0,3)`-tensor `baseRic g = (A,B,C) ↦ Ric(A,B)` whose third value slot is a *dummy* slot.  Because
that slot is unused, the recursion `step` of that tower produces, besides the honest derivative,
a "shift" correction from the unused slot, and the resulting object is **not** additive in its
direction slots (see the discussion in `RicFlip/HonestFlip.lean`), so it cannot be flipped between
two connections.

The *honest* tower is obtained by forgetting the dummy slot: reading `Ric` as a `(0,2)`-tensor
`ric2 g` (`Fam 2`), the packed recursion `AMB.pD` reproduces the honest recursion `hstep`
slot for slot (`pD` corrects *all* slots of the object, and after dropping the dummy slot the
corrected slots are exactly the derivative slots and the two value slots).  Hence

  `RicT g i := AMB.pDiter (lcOf g) (ric2 g) i : Fam (i+2)`

is the honest `i`-th covariant derivative of `Ric`, and it *is* additive in every slot — which is
what the two-connection flip `pD_flip_full` requires.

The bridge to the `Op3` honest tower `htower (lcOf g) (baseRic g) i` is the reindexing that drops
the last (`C`) slot of the packed `(i+3)`-tuple.
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

/-- The pointwise Ricci tensor of `g`, read as a packed `Fam 2` object: its two slots are the two
value slots of the `(0,2)`-tensor. -/
noncomputable def ric2 (g : Submission.Diff.SMet I M) : Fam (I := I) (M := M) 2 :=
  fun F x => ricAt (Submission.Diff.lcOf g) x (F 0 x) (F 1 x)

/-- The `k`-fold iteration of the packed recursion `AMB.pD` on a `Fam 2` base. -/
noncomputable def pDiter2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (T : Fam (I := I) (M := M) 2) : ∀ k : ℕ, Fam (I := I) (M := M) (k + 2)
  | 0 => T
  | k + 1 => AMB.pD cov (pDiter2 cov T k)

/-- **The honest pack of the `i`-th covariant derivative of the Ricci tensor**: the `AMB.pD`-iterated
tower of `ric2 g`. -/
noncomputable def RicT (g : Submission.Diff.SMet I M) (i : ℕ) : Fam (I := I) (M := M) (i + 2) :=
  pDiter2 (Submission.Diff.lcOf g) (ric2 g) i

theorem RicT_zero (g : Submission.Diff.SMet I M) : RicT g 0 = ric2 g := rfl

theorem RicT_succ (g : Submission.Diff.SMet I M) (i : ℕ) :
    RicT g (i + 1) = AMB.pD (Submission.Diff.lcOf g) (RicT g i) := rfl

end Work.Diff.EXT.ConnCov.RicFlip
