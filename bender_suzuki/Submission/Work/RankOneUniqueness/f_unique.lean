import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.f_unique` — the map `f` is well defined

If `t x t = m·t·y = m'·t·y'` with `m, m' ∈ H` and `y, y' ∈ Q`, then `y = y'` (and `m = m'`)
by uniqueness of the canonical form `H·t·Q` (`canon_unique`).  So the map `f : Q# → Q#` of
Peterfalvi II Ch. VII §1 is well defined.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem f_unique {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x y y' : G} (hy : y ∈ Q) (hy' : y' ∈ Q)
    (h1 : FRel H t x y) (h2 : FRel H t x y') : y = y' := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨m', hm', hm2⟩ := h2
  exact (canon_unique h hm hm' hy hy' (by rw [← hm1, hm2])).2

end Work.RankOneUniqueness
