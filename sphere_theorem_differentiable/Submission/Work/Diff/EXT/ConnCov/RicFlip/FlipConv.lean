import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit
import Submission.Work.Diff.EXT.ConnCov.RicTr.ShiftDefs
import Submission.Work.Diff.EXT.ConnCov.baseRic_tower_hypotheses

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tuple bookkeeping of the two conversions (modified ↔ honest tower)

The chain of the flip chapter is

* the **moving modified** tower `AMB.pack (ATower.tower (lcOf (G t)) (baseRic (G t)) j)` — bounded by
  the hypotheses of `ricTowerFlipBound` (`hRt`);
* the **moving honest** tower `RicT (G t) j` (`= pDiter2 (lcOf (G t)) (ric2 (G t)) j`) — the leaves
  of the term calculus, to which the shift identity converts the first;
* the **fixed honest** tower `pDiter2 (lcOf (G 0)) (ric2 (G t)) j` — the output of the flip
  induction;
* the **fixed modified** tower `AMB.pack (ATower.tower (lcOf (G 0)) (baseRic (G t)) k)` — the
  object of the target, to which the shift identity converts the third.

The two conversions are both applications of the **shift identity** (`towerExpansionSm`):
the modified tower is the signed selection sum of the honest towers,

`pack (tower cov (baseRic g) m) F = Σ_{j ≤ m} (-1)^{m+j} (m-j)! · Σ_{f : Fin j ↪o Fin m}
    pDiter2 cov (ric2 g) j (subTuple F f)`,

where `subTuple F f` is the tuple of the honest tower: its direction slots are the `f`-selected
direction slots of `F` and its two value slots are the `A`- and `B`-slots of `F`.

This module only collects the *vocabulary* of that identity, so that the conversion lemmas can be
stated compactly:

* `subTuple` — the substituted tuple;
* `liftTup` — the tuple of the honest tower lifted to the modified tower's arity: the first `m + 2`
  slots are copied and the (unused) third value slot is filled with `0` (so that the extra factor of
  a `Bnd1` bound on the modified tower is `1`);
* `shiftSum` — the right-hand side of the shift identity.

The component lemmas `subTuple_castAdd`, `subTuple_natAdd_zero`, `subTuple_natAdd_one`,
`liftTup_castAdd`, `liftTup_natAdd` record the entries of these tuples.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The tuple on which the honest tower of level `j` is evaluated in the shift identity.**  Given
a tuple `F` for the modified tower at level `m` (so `F : Fin (m+3) → TF`: direction slots `0..m-1`
and the value slots `A`, `B`, `C`), the `f`-selection of `j` direction slots gives the tuple of the
honest tower at level `j`: the selected direction slots, then the `A`- and `B`-slots. -/
noncomputable def subTuple {j m : ℕ} (F : Fin (m+3) → AMB.TF (I := I) (M := M))
    (f : Fin j → Fin m) : Fin (j+2) → AMB.TF (I := I) (M := M) :=
  Fin.addCases (m := j) (n := 2) (motive := fun _ => AMB.TF (I := I) (M := M))
    (fun l : Fin j => F (Fin.castAdd 3 (f l)))
    (fun q : Fin 2 => F (Fin.natAdd m (Fin.castSucc q)))

/-- **The lift of a tuple of the honest tower to the modified tower's arity**: the first `m + 2`
slots are copied and the (unused) third value slot is filled with `0`.  With this choice the extra
factor of a `Bnd1` bound on the modified tower is `1`. -/
noncomputable def liftTup {m : ℕ} (P : Fin (m+2) → AMB.TF (I := I) (M := M)) :
    Fin (m+3) → AMB.TF (I := I) (M := M) :=
  Fin.addCases (m := m+2) (n := 1) (motive := fun _ => AMB.TF (I := I) (M := M))
    (fun l : Fin (m+2) => P l)
    (fun _ : Fin 1 => fun y : M => (0 : TangentSpace I y))

/-- **The right-hand side of the packed shift identity**: the signed sum, over all selections of
`j` direction slots, of the honest tower at level `j` evaluated on `subTuple F f`. -/
noncomputable def shiftSum (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : SMet I M) (m : ℕ) (F : Fin (m+3) → AMB.TF (I := I) (M := M)) : M → ℝ :=
  fun x => ∑ j ∈ Finset.range (m + 1),
      ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
        ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m,
          pDiter2 cov (ric2 g) j (subTuple F f.val) x

/-- The direction slots of `subTuple F f`. -/
theorem subTuple_castAdd {j m : ℕ} (F : Fin (m+3) → AMB.TF (I := I) (M := M))
    (f : Fin j → Fin m) (l : Fin j) :
    subTuple F f (Fin.castAdd 2 l) = F (Fin.castAdd 3 (f l)) :=
  Fin.addCases_left l

/-- The first value slot of `subTuple F f`. -/
theorem subTuple_natAdd_zero {j m : ℕ} (F : Fin (m+3) → AMB.TF (I := I) (M := M))
    (f : Fin j → Fin m) :
    subTuple F f (Fin.natAdd j 0) = F (Fin.natAdd m (Fin.castSucc 0)) :=
  Fin.addCases_right (0 : Fin 2)

/-- The second value slot of `subTuple F f`. -/
theorem subTuple_natAdd_one {j m : ℕ} (F : Fin (m+3) → AMB.TF (I := I) (M := M))
    (f : Fin j → Fin m) :
    subTuple F f (Fin.natAdd j 1) = F (Fin.natAdd m (Fin.castSucc 1)) :=
  Fin.addCases_right (1 : Fin 2)

/-- The first `m + 2` slots of `liftTup P` are those of `P`. -/
theorem liftTup_castAdd {m : ℕ} (P : Fin (m+2) → AMB.TF (I := I) (M := M)) (l : Fin (m+2)) :
    liftTup P (Fin.castAdd 1 l) = P l :=
  Fin.addCases_left l

/-- The third value slot of `liftTup P` is zero. -/
theorem liftTup_natAdd {m : ℕ} (P : Fin (m+2) → AMB.TF (I := I) (M := M)) :
    liftTup P (Fin.natAdd (m + 2) (0 : Fin 1)) = fun y : M => (0 : TangentSpace I y) :=
  Fin.addCases_right (0 : Fin 1)

end Work.Diff.EXT.ConnCov.RicFlip
