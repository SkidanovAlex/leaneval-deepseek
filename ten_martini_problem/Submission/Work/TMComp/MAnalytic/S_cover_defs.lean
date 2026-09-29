import Mathlib
import Submission.Work.TMComp.MAnalytic.propagate_defs

/-!
# Auxiliary sets for the covering lemma `S_cover`

This file introduces the two sets used in the proof of
`Work.TMComp.MAnalytic.S_cover`:

* `Eset W r a` -- the set of points reachable in finitely many steps;
* `Dset W r a` -- the set of centres of reachable *deep* balls, i.e. centres `y` for
  which there is a reachable state `(y, R)` with `closedBall y (2 * R) ⊆ W`.

`Dset` is the set on which the "propagation of smallness" argument is carried out: it
is open (one can always step to a nearby deep state) and its complement is open
because one can first inflate the reachable radius whenever there is room.
-/

namespace Work.TMComp.MAnalytic

/-- The points of `W` that are reached (as centres of some reachable state) in finitely
many steps. -/
def Eset (W : Set ℂ) (r : ℝ) (a : ℂ) : Set ℂ := ⋃ n, S W r a n

/-- Centres of reachable *deep* balls: `y ∈ Dset W r a` if there is `m`, `R` with
`(y, R) ∈ G W r a m` and `closedBall y (2 * R) ⊆ W`. -/
def Dset (W : Set ℂ) (r : ℝ) (a : ℂ) : Set ℂ :=
  {y | ∃ m R, (y, R) ∈ G W r a m ∧ Metric.closedBall y (2 * R) ⊆ W}

theorem mem_Eset {W : Set ℂ} {r : ℝ} {a : ℂ} {z : ℂ} :
    z ∈ Eset W r a ↔ ∃ n, z ∈ S W r a n := by
  simp [Eset]

theorem mem_Dset {W : Set ℂ} {r : ℝ} {a : ℂ} {y : ℂ} :
    y ∈ Dset W r a ↔ ∃ m R, (y, R) ∈ G W r a m ∧ Metric.closedBall y (2 * R) ⊆ W :=
  Iff.rfl

theorem Dset_subset_Eset (W : Set ℂ) (r : ℝ) (a : ℂ) : Dset W r a ⊆ Eset W r a := by
  rintro y ⟨m, R, hG, -⟩
  exact mem_Eset.mpr ⟨m, R, hG⟩

end Work.TMComp.MAnalytic
