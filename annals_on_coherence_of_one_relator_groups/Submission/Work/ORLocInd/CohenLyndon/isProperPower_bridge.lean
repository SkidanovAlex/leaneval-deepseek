import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.OROneRel.Basic

universe u

namespace Work.ORLocInd.CohenLyndon

/-- The two notions of "proper power" used in the two subprojects agree on nontrivial elements.

`Work.ORLocInd.IsProperPower w` asks for `w = v ^ m` with `v ≠ 1` and `m ≥ 2`, while
`Work.OROneRel.IsProperPower r` asks only for `r = v ^ m` with `m ≥ 2`; the two differ exactly at
the trivial element (`1 = 1 ^ 2` is a proper power in the second sense but not in the first).  Hence
the hypothesis `u ≠ 1`.

The forward implication is immediate (the extra hypothesis `v ≠ 1` is simply dropped); for the
backward one, if `u = v ^ m` with `m ≥ 2` and `v = 1` then `u = 1`, contradicting `hu`. -/
theorem isProperPower_bridge {X : Type u} {u : FreeGroup X} (hu : u ≠ 1) :
    Work.ORLocInd.IsProperPower u ↔ Work.OROneRel.IsProperPower u := by
  constructor
  · rintro ⟨v, _hv, m, hm, rfl⟩
    exact ⟨v, m, hm, rfl⟩
  · rintro ⟨v, m, hm, rfl⟩
    exact ⟨v, fun hv => hu (by rw [hv, one_pow]), m, hm, rfl⟩

end Work.ORLocInd.CohenLyndon
