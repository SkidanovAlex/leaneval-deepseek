/-
Area AUTA7: the deliverable `Work.GW2.AutA7Prop`.

The case distinction is on the parity of the index `[Q : L]`:

* odd index (`Work.AUTA7.A7.OddIndex`, using `Work.AUTA7.A7.SylowFacts`): Frattini plus coprime
  action force `Q = L`;
* even index (`Work.AUTA7.A7.EvenIndex`, using `Work.AUTA7.A7.InvolutionLocal` and
  `Work.AUTA7.A7.D16MaxIntersect`): the residual case is contradictory.

Both cases are proved in this area, so `AutA7Prop` is unconditional.
-/
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.A7.OddIndex
import Submission.Work.AUTA7.A7.EvenIndex

namespace Work.GW2

/-- **The deliverable `AutA7Prop` from the two index-parity cases.** If the odd-index case forces
`L = ⊤` and the even-index case is impossible, then `L = ⊤` in full generality. -/
theorem AutA7Prop_of_index_cases (hEven : AutA7EvenIndexProp) (hOdd : AutA7OddIndexProp) :
    AutA7Prop := by
  intro Q _ _ L hN hL hC hS
  by_cases h : 2 ∣ L.index
  · exact absurd h (hEven Q L hN hL hC hS)
  · refine hOdd Q L hN hL hC hS (Nat.not_even_iff_odd.mp ?_)
    intro he
    exact h (Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp he))

/-- **The area's deliverable**: a finite group `Q` with a normal subgroup `L ≅ A₇`, with trivial
centralizer `C_Q(L) = 1` and with cyclic-or-dihedral Sylow 2-subgroups satisfies `L = ⊤`. In
particular `A₇` has no proper overgroup of this kind. -/
theorem autA7Prop : Work.GW2.AutA7Prop :=
  AutA7Prop_of_index_cases Work.AUTA7.A7.EvenIndex Work.AUTA7.A7.OddIndex

end Work.GW2
