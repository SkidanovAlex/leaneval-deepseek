import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.InjRadius

/-!
# `Work.EKLC6Core.ShallowRelDefs` — the *relatively* shallow set of a cell family

For a countable family `Q : ℕ → Set X₃` of cells and a *relative* scale `ε > 0`, a point `y` is
**`ε`-relatively shallow** if it lies in some cell `Q k` but the ball of the *relative* radius
`ε * injCap y` — i.e. the `V`-ball whose radius is measured in units of the injectivity radius of
`y` itself — is not contained in that cell.

This is the scale-free (cusp-compatible) variant of `Work.EKLC6Core.shallow`
(`Work.EKLC6Core.epsDepthDefs`), which uses an *absolute* radius.  The relative form is what the
depth statement `Work.EKLC6Core.cellW_relative_depth_ae` needs: the required radius shrinks with
the injectivity radius of the orbit point, so that an atom sitting at a super-exponentially deep
cusp point is *not* automatically shallow (its own cell has a radius comparable to its injectivity
radius, hence a positive *relative* margin).

## Main contents

* `shallowRel` — the definition;
* `not_shallowRel_iff` — the negation is exactly the relative depth condition;
* `shallowRel_mono` — monotonicity in the relative scale (used to trade a rate `λ` for a smaller
  rate `λ' ≤ λ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- A point `y` is **`ε`-relatively shallow** w.r.t. the cell family `Q` if it lies in a cell `Q k`
whose `ε * injCap y`-ball it does not contain.  (Points outside `⋃ k, Q k` are *not* shallow.) -/
def shallowRel (Q : ℕ → Set X3) (ε : ℝ) : Set X3 :=
  {y : X3 | ∃ k, y ∈ Q k ∧ ∃ v ∈ V (ε * injCap y), v • y ∉ Q k}

/-- Negation of relative shallowness: the point is `ε`-deep inside whichever cell contains it. -/
theorem not_shallowRel_iff {Q : ℕ → Set X3} {ε : ℝ} {y : X3} :
    y ∉ shallowRel Q ε ↔
      ∀ k, y ∈ Q k → ∀ v ∈ V (ε * injCap y), v • y ∈ Q k := by
  constructor
  · rintro h k hk v hv
    by_contra hcon
    exact h ⟨k, hk, v, hv, hcon⟩
  · rintro h ⟨k, hk, v, hv, hcon⟩
    exact hcon (h k hk v hv)

/-- The relatively shallow set is monotone in the relative scale. -/
theorem shallowRel_mono {Q : ℕ → Set X3} {ε ε' : ℝ} (h : ε ≤ ε') :
    shallowRel Q ε ⊆ shallowRel Q ε' := by
  rintro y ⟨k, hk, v, hv, hvy⟩
  refine ⟨k, hk, v, ?_, hvy⟩
  intro i j
  refine lt_of_lt_of_le (hv i j) ?_
  have hpos : 0 < injCap y := injCap_pos y
  nlinarith

/-- At relative scale `0` the relatively shallow set is empty. -/
theorem shallowRel_zero (Q : ℕ → Set X3) : shallowRel Q 0 = ∅ := by
  ext y
  constructor
  · rintro ⟨k, -, v, hv, -⟩
    have h := hv 0 0
    simp only [zero_mul] at h
    exact absurd h (not_lt.mpr (abs_nonneg _))
  · intro h
    exact absurd h (Set.notMem_empty y)

end Work.EKLC6Core
