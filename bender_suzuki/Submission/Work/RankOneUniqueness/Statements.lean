import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.Statements` — shared statements of the rank-one recognition

This module is the **interface** of the area `RankOneUniqueness` for the recognition of a
rank-one group from its `Q`-data.  It contains the new blueprint `Prop`

* `RankOneQUniquenessProp` — S1 of the lead's design
  (`Submission/Work/RankOneUniqueness/_design/QUniqueness.lean`);
* `ModelRankOneDatum` — S5, the datum of a model group coordinated by a group `C` with its
  `f`-map `fC`.

Downstream areas (`ZassenhausPSL2`, `ZassenhausSuzuki`, `PSU3`, `Models`) import this module
(and `Submission.Work.RankOneUniqueness.recognize` for the recognition lemma).

Rationale (Peterfalvi II Ch. VII §1, Lemma p. 268).  The book shows that
`⟨Q^x | x ∈ L⟩` is determined, up to isomorphism, by `Q` and the map `f : Q# → Q#`
characterised by `t x t = g(x) h(x) t f(x)`.  For a **simple** `L` this subgroup is `L`
itself (`⟨Q, tQt⟩` is normal and nontrivial, and `t ∈ L`), so `L` is determined by `(Q, f)`
alone: no isomorphism of the point stabiliser `H` — in particular none of the two-point
stabiliser `D` — is needed.  That is the content of `RankOneQUniquenessProp`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.RankOneUniqueness

/-- **S1.**  Two finite simple groups with split rank-one data whose root groups are
isomorphic by an isomorphism carrying the `f`-relation `t x t = m t y` of the first to that of
the second are isomorphic.

This is Peterfalvi II Ch. VII §1, Lemma p. 268, in the form in which the recognition areas
(`ZassenhausPSL2`, `ZassenhausSuzuki`, `PSU3`) use it: only `Q` and `f` have to be matched. -/
def RankOneQUniquenessProp : Prop :=
  ∀ (G G' : Type) [Group G] [Finite G] [Group G'] [Finite G']
    (H Q : Subgroup G) (t : G) (H' Q' : Subgroup G') (t' : G'),
    IsSimpleGroup G → IsSimpleGroup G' →
    IsSplitRankOne H Q t → IsSplitRankOne H' Q' t' →
    ∀ ψ : Q ≃* Q',
      (∀ x y : Q, (x : G) ≠ 1 → (∃ m ∈ H, t * (x : G) * t = m * t * (y : G)) →
        ∃ m' ∈ H', t' * (ψ x : G') * t' = m' * t' * (ψ y : G')) →
      Nonempty (G ≃* G')

/-- **S5.**  A model rank-one datum: split rank-one data in a finite simple group `Y`, with the
root group `Q` coordinatised by a group `C` on which the model's `f`-map is the given
`fC : C → C`.  (`c` need not be compatible with `fC` beyond `frel`.) -/
structure ModelRankOneDatum (Y : Type) [Group Y] [Finite Y] (C : Type) [Group C]
    (fC : C → C) where
  /-- the point stabiliser -/
  H : Subgroup Y
  /-- the root group -/
  Q : Subgroup Y
  /-- the involution outside `H` -/
  t : Y
  /-- the split rank-one structure -/
  split : IsSplitRankOne H Q t
  /-- simplicity of the model -/
  simple : IsSimpleGroup Y
  /-- the coordination of the root group -/
  c : C ≃* Q
  /-- the model's `f`-relation, read in the coordinates `C` -/
  frel : ∀ u : C, u ≠ 1 → ∃ m ∈ H, t * (c u : Y) * t = m * t * (c (fC u) : Y)

end Work.RankOneUniqueness
