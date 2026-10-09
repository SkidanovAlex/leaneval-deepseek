import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.omegaZ_primeUnit
import Submission.Work.HilbertSymbol.signOf_intCast
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The supplementary law for `2`: for an odd prime `p`, `(2/p) = χ₈(p)` equals `1` when
`p ≡ ±1 (mod 8)` and `-1` when `p ≡ ±3 (mod 8)`. -/
theorem legendreSym_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  rw [legendreSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]

theorem signOf_omegaZ_primeUnit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    signOf (omegaZ (unitPart 2 (primeUnit p))) = intUnitOf (legendreSym p 2) := by
  rw [omegaZ_primeUnit_indicator p hp, legendreSym_two p hp]
  by_cases hc : p % 8 = 1 ∨ p % 8 = 7
  · simp [if_pos hc]
  · simp [if_neg hc]

end Work.HilbertSymbol
