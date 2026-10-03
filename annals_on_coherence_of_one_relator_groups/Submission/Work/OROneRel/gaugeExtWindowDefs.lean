/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The vocabulary of the global gauge extension of a window

This file fixes the definitions used by `Work.OROneRel.exists_globalGauge_of_windowData`.

We are given a weight `c : α → ℤ`, a level window `[lo,hi]` and a gauge `Wt` on it (the words
`Wt i`, `lo ≤ i ≤ hi`, whose walks use only edges of trivial loop class, `winTree`).  The goal is to
extend `Wt` to a gauge `gxGauge Wt c lo hi x₀` on *all* of `ℤ` whose every word's walk uses only
edges of trivial loop class.  The extension is made by *chains of `x₀`-edges*, in the two directions
away from the window:

* a level `j > hi` is reached from the level `gxUpBase (c x₀) hi j ∈ (hi - c x₀, hi]` by
  `gxUpExp (c x₀) hi j` upward steps of the edge `(x₀, ·)`;
* a level `j < lo` is reached from the level `gxDnBase (c x₀) lo j ∈ [lo, lo + c x₀)` by
  `gxDnExp (c x₀) lo j` downward steps.

Both base levels lie in the window, so the chain starts at a word whose walk is already trivial, and
the chain edges have their *outer* endpoint outside the window, so the chain equations can be imposed
without contradicting the given data.  This is where the hypotheses `0 < c x₀` and
`c x₀ ≤ hi - lo` are used: the window is at least as wide as one `x₀`-step.

The two base maps are given by the closed formulae

* `gxUpBase d hi j = j - ((j - hi - 1) / d + 1) * d`, `gxUpExp d hi j = (j - hi - 1) / d + 1`;
* `gxDnExp d lo j = (lo - j - 1) / d + 1`, `gxDnBase d lo j = j + gxDnExp d lo j * d`,

so that `gxUpBase d hi j + gxUpExp d hi j * d = j` and `gxDnBase d lo j - gxDnExp d lo j * d = j`
hold by `ring`.  The arithmetic properties that make the chains work are proved in
`Submission/Work/OROneRel/gxUpBase_arith.lean` and `Submission/Work/OROneRel/gxDnBase_arith.lean`.
-/

import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The triviality predicate of a walk.**  Every traversed edge of the word `L`, read from the level
`i` (`decor c i L`), has trivial loop class under the gauge `D`. -/
def gxTrivFrom (c : α → ℤ) (D : ℤ → FreeGroup α) (i : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ p ∈ decor c i L, coverClassAt D c (coverEdge p) = 1

/-- **The base level of the `x₀`-chain above the window.**  For `j > hi` this is the unique level `w`
with `hi - d < w ≤ hi` and `j ≡ w (mod d)`. -/
def gxUpBase (d hi j : ℤ) : ℤ := j - (((j - hi - 1) / d) + 1) * d

/-- **The number of `x₀`-steps of the chain above the window.** -/
def gxUpExp (d hi j : ℤ) : ℤ := ((j - hi - 1) / d) + 1

/-- **The number of `x₀`-steps of the chain below the window.** -/
def gxDnExp (d lo j : ℤ) : ℤ := ((lo - j - 1) / d) + 1

/-- **The base level of the `x₀`-chain below the window.**  For `j < lo` this is the unique level `u`
with `lo ≤ u < lo + d` and `j ≡ u (mod d)`. -/
def gxDnBase (d lo j : ℤ) : ℤ := j + gxDnExp d lo j * d

/-- **The global gauge extending the window gauge `Wt`.**  On the window it is `Wt` itself; above the
window the level `j` carries the word of the base level times `x₀ ^ (gxUpExp …)`, below the window
the word of the base level times `x₀ ^ (-(gxDnExp …))`. -/
noncomputable def gxGauge (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (x₀ : α) :
    ℤ → FreeGroup α :=
  fun j =>
    if lo ≤ j ∧ j ≤ hi then Wt j
    else if hi < j then
      Wt (gxUpBase (c x₀) hi j) * (FreeGroup.of x₀) ^ (gxUpExp (c x₀) hi j)
    else
      Wt (gxDnBase (c x₀) lo j) * (FreeGroup.of x₀) ^ (-(gxDnExp (c x₀) lo j))

theorem gxGauge_of_mem {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {x₀ : α} {j : ℤ}
    (h : lo ≤ j ∧ j ≤ hi) : gxGauge Wt c lo hi x₀ j = Wt j := by
  rw [gxGauge]
  exact if_pos h

theorem gxGauge_of_gt {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {x₀ : α} {j : ℤ}
    (h : hi < j) :
    gxGauge Wt c lo hi x₀ j =
      Wt (gxUpBase (c x₀) hi j) * (FreeGroup.of x₀) ^ (gxUpExp (c x₀) hi j) := by
  rw [gxGauge]
  rw [if_neg (by rintro ⟨-, h2⟩; exact absurd h2 (not_le.mpr h)), if_pos h]

theorem gxGauge_of_lt {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {x₀ : α} {j : ℤ}
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (h : j < lo) :
    gxGauge Wt c lo hi x₀ j =
      Wt (gxDnBase (c x₀) lo j) * (FreeGroup.of x₀) ^ (-(gxDnExp (c x₀) lo j)) := by
  rw [gxGauge]
  rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (not_le.mpr h)),
    if_neg (by omega : ¬ hi < j)]

end Work.OROneRel
