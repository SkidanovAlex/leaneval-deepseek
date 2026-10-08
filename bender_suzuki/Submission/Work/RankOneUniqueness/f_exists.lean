import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.conj_notMem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.f_exists` — the map `f` is defined on `Q#`

For `x ∈ Q#`, `t x t ∉ H` (`conj_notMem`), so it has a canonical form `t x t = m·t·y` with
`m ∈ H`, `y ∈ Q` (`canon_exists`); this is Peterfalvi's `y = f(x)`, and the relation is
exactly `FRel H t x y`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem f_exists {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    ∃ y ∈ Q, FRel H t x y := by
  obtain ⟨a, ha, q, hq, hg⟩ := canon_exists h (conj_notMem h hx hx1)
  exact ⟨q, hq, a, ha, hg⟩

end Work.RankOneUniqueness
