import Mathlib
import Submission.Work.ClassFieldTower.Defs

namespace Work.ClassFieldTower

/-- **The Shafarevich--Koch bound, in deficiency form.**

Unfolding the definitions, `ShafarevichKochBound F d r` is `r ≤ d + unitTwoRank F` and
`deficiency d r` is `r - d`, so under the (automatic, for a presentation with at most as
many relators as generators needed) hypothesis `d ≤ r` the two statements are the same
truncated-subtraction identity `r - d ≤ u ↔ r ≤ d + u`. -/
theorem shafarevichKochBound_iff_deficiency {F : Type*} [Field F] [NumberField F] {d r : ℕ}
    (hdr : d ≤ r) : ShafarevichKochBound F d r ↔ deficiency d r ≤ unitTwoRank F := by
  have hcancel : r - d + d = r := Nat.sub_add_cancel hdr
  simp only [ShafarevichKochBound, deficiency]
  omega

end Work.ClassFieldTower
