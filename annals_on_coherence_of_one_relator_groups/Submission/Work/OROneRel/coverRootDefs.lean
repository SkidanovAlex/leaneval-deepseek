/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The candidate root of the `Z`-cover decomposition

This file contains *definitions only* (no `sorry`), so that lemma requests may import it and state
lemmas about them.

Let `c : α → ℤ` be a weight with `cohom c u = 1` (i.e. `c` kills `u`), let `u : FreeGroup α` and let
`W : ℤ → FreeGroup α` be a *gauge* (`W 0 = 1`), i.e. a word attached to every level of the `ℤ`-cover.
The decorated word `decor c 0 (wordOf u)` is a walk on the levels `ℤ` (see
`Submission/Work/OROneRel/gaugeLevelDefs.lean`); the *loop class* of a decorated letter `p` is

  `coverClass W c p = gaugeMap W c (letter of p) = W (coverSrc c p) * (letter) * (W (coverTgt c p))⁻¹`

(`GaugeDefs.gauge_letter`).  The symbols of non-trivial loop class form the generating set

  `coverBeta W c u`,

of the base group of the Magnus--Moldavanskii step in the case where no letter of `u` has vanishing
exponent sum, and the word they spell,

  `coverRoot W c u`,

is the candidate *root* `v` of the base: it is the decorated word of `u` with the letters of trivial
loop class deleted (`gauge_truncation` shows that the product of the loop classes of the remaining
letters is still `u`, so `coverToClasses (coverRoot W c u) = u`).  Since the trivial letters may be
chosen through a *first-arrival gauge* (`gauge_walk_defs.walkGauge`), at least one letter per visited
level is trivial, whence

  `relatorNorm (coverRoot W c u) ≤ #(non-trivial letters) ≤ |u| - (V - 1) < |u|`

where `V ≥ 2` is the number of levels visited by the walk -- the strictly shorter root.
-/
import Mathlib
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.gauge_walk_defs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The loop class of a decorated letter `p` in the covering group: `gaugeMap W c` of the letter,
which by `gauge_letter` is `W (coverSrc c p) * (letter) * (W (coverTgt c p))⁻¹`. -/
noncomputable def coverClass (W : ℤ → FreeGroup α) (c : α → ℤ) (p : (α × ℤ) × Bool) :
    FreeGroup α :=
  gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)

/-- The decorated letters of `u` whose loop class is non-trivial: the generating set `β` of the base
group of the `Z`-cover decomposition. -/
def coverBeta (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) : Type u :=
  {p : (α × ℤ) × Bool // p ∈ decor c 0 (wordOf u) ∧ coverClass W c p ≠ 1}

/-- A classical decidable equality on `β`, needed to speak about the reduced word of `coverRoot`. -/
noncomputable instance coverBetaDecidableEq (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    DecidableEq (coverBeta W c u) := Classical.decEq _

/-- The word spelled by the decorated letters of `u` of non-trivial loop class.

Each decorated letter is a *directed* edge of the cover, so its β-generator already carries its
direction (`coverClass` is the loop class of the traversal, not of the undirected edge); the exponent
in the spelled word is therefore always `+`.  With this convention `gauge_truncation` gives
`coverToClasses W c u (coverRoot W c u) = u`. -/
noncomputable def coverRootList (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    List (coverBeta W c u × Bool) := by
  classical
  exact (decor c 0 (wordOf u)).attach.filterMap (fun p =>
    if h : coverClass W c p.1 ≠ 1 then some (⟨p.1, p.2, h⟩, true) else none)

/-- **The candidate root of the `Z`-cover decomposition**: the element of `F (β)` spelled by the
decorated letters of `u` of non-trivial loop class. -/
noncomputable def coverRoot (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    FreeGroup (coverBeta W c u) := FreeGroup.mk (coverRootList W c u)

/-- The class map `F (β) →* F α` sending a symbol to its loop class. -/
noncomputable def coverToClasses (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    FreeGroup (coverBeta W c u) →* FreeGroup α :=
  FreeGroup.lift fun p => coverClass W c p.1

/-- The level set of the walk of the decorated word of `u`: the union of the source and target levels
of its decorated letters. -/
def coverLevelSet (c : α → ℤ) (u : FreeGroup α) : Set ℤ :=
  {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i} ∪
    {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}

theorem mem_coverLevelSet {c : α → ℤ} {u : FreeGroup α} {i : ℤ} :
    i ∈ coverLevelSet c u ↔
      (∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i) ∨
        ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i := Iff.rfl

end Work.OROneRel
