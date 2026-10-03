import Mathlib
import Submission.Work.FIArea2.TsumDefs2
import Submission.Work.FIArea2.congAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea2

/-- **A unit modulo `p ^ ν` has at most four square roots** (`p` prime, `ν ≥ 1`).

This is the `p`-adic square-root count used throughout §9 of Friedlander--Iwaniec.  For an odd
prime `p` a unit of `ZMod (p ^ ν)` has at most two square roots (`sq_root_card_le_two`, from
`congAux`), while for `p = 2` it has at most four (`sq_root_card_le_four`, from `congAux`),
using that the group of units of `ZMod (2 ^ ν)` has at most `2`-torsion of order four. -/
theorem roots_card_le_four_unit (p ν : ℕ) (hp : p.Prime) [NeZero (p ^ ν)] (hν : 1 ≤ ν) (a : ℤ)
    (ha : IsUnit (a : ZMod (p ^ ν))) :
    (Finset.univ.filter (fun ρ : ZMod (p ^ ν) => ρ ^ 2 = (a : ZMod (p ^ ν)))).card ≤ 4 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact sq_root_card_le_four hν (a : ZMod (2 ^ ν)) ha
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    have h := sq_root_card_le_two hp hp2 hν (a : ZMod (p ^ ν)) ha
    omega

end Work.FIArea2
