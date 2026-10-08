import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.RankOneUniqueness.rankOneQUniqueness

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.recognize` — uniform recognition of a rank-one group (S6)

Given `RankOneQUniquenessProp`, a model datum `M : ModelRankOneDatum Y C fC` (split rank-one
data in a simple `Y` with the root group coordinatised by `C` and the model's `f`-map `fC`)
and a coordination `e : Q ≃* C` of the root group of `G` which turns `FRel` into `fC`
(`, `e y = fC (e x)` whenever `t x t ∈ H t y`), we obtain `G ≃* Y`.

This is the single lemma with which the recognition areas (`ZassenhausPSL2`,
`ZassenhausSuzuki`, `PSU3`) conclude: they only have to coordinatise `Q` and compute `f`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem recognize (hQU : RankOneQUniquenessProp)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    {Y : Type} [Group Y] [Finite Y] {C : Type} [Group C] {fC : C → C}
    (M : ModelRankOneDatum Y C fC) (e : Q ≃* C)
    (he : ∀ x y : Q, (x : G) ≠ 1 → FRel H t (x : G) (y : G) → e y = fC (e x)) :
    Nonempty (G ≃* Y) := by
  have hψf : ∀ x y : Q, (x : G) ≠ 1 →
      (∃ m ∈ H, t * (x : G) * t = m * t * (y : G)) →
      ∃ m' ∈ M.H, M.t * ((e.trans M.c) x : Y) * M.t = m' * M.t * ((e.trans M.c) y : Y) := by
    intro x y hx1 hrel
    have h1 : e y = fC (e x) := he x y hx1 hrel
    have hx0 : e x ≠ 1 := by
      intro h0
      exact hx1 (by
        have h2 : e x = e 1 := by rw [h0, map_one]
        exact congrArg Subtype.val (e.injective h2))
    obtain ⟨m', hm', hm'eq⟩ := M.frel (e x) hx0
    refine ⟨m', hm', ?_⟩
    rw [← h1] at hm'eq
    simpa using hm'eq
  exact hQU G Y H Q t M.H M.Q M.t ((inferInstance : IsSimpleGroup G)) M.simple h M.split
    (e.trans M.c) hψf

end Work.RankOneUniqueness
