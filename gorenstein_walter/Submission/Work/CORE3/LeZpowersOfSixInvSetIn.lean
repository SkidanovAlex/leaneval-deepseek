import Mathlib
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SixInvSetEnumeration

/-!
# An odd-order subgroup of a six-element inverted set is cyclic of order three

`Work.CORE3.LeZpowersOfSixInvSetIn`.  Let `y` be an involution, `Hh` a subgroup, and
`I = invSetIn Hh y = {x ∈ Hh | y x y = x⁻¹}` the set of elements of `Hh` inverted by `y`.  If

* `a ∈ I` has order `3`,
* `b₁ ≠ b₂` are two elements of `I` of order `2`,

and `|I| = 6`, then `I = {1, a, a², b₁, b₂, c}` with `c` a further involution
(`Work.CORE3.SixInvSetEnumeration`).  Consequently every element of `I` of *odd* order is `1`,
`a` or `a²`; so any subgroup `X ≤ G` with `X ⊆ I` whose order is odd satisfies `X ≤ ⟨a⟩`.

This is the counting step of Bender 1981 §3 (6) used in `Case1bLeFourNotLeD`: an odd-order
subgroup lying in `I_Ĥ(y)` is contained in the unique `⟨a⟩ ≅ C₃` of `I_Ĥ(y)`.
-/

namespace Work.CORE3

set_option linter.unusedVariables false in
theorem LeZpowersOfSixInvSetIn {G : Type} [Group G] {Hh : Subgroup G} {y a b1 b2 : G}
    (hy : y * y = 1) (haI : a ∈ Work.CORE3.invSetIn Hh y) (ha3 : orderOf a = 3)
    (hb1I : b1 ∈ Work.CORE3.invSetIn Hh y) (hb1o : orderOf b1 = 2)
    (hb2I : b2 ∈ Work.CORE3.invSetIn Hh y) (hb2o : orderOf b2 = 2) (h12 : b1 ≠ b2)
    (hsix : (Work.CORE3.invSetIn Hh y).ncard = 6)
    {X : Subgroup G} (hXI : ∀ x ∈ X, x ∈ Work.CORE3.invSetIn Hh y)
    (hXodd : Odd (Nat.card X)) (hXne : X ≠ ⊥) :
    X ≤ Subgroup.zpowers a := by
  -- The six-element inverted set is `{1, a, a², b₁, b₂, c}` with `c` an involution.
  obtain ⟨c, _hcI, hc_ord, hmem⟩ :=
    SixInvSetEnumeration hy haI ha3 hb1I hb1o hb2I hb2o h12 hsix
  intro x hxX
  have hxI : x ∈ invSetIn Hh y := hXI x hxX
  -- An element of `X` has odd order, because `orderOf x` divides `|X|`.
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat hXodd (X.orderOf_dvd_natCard hxX)
  -- Every element of `I` is `1`, `a`, `a²`, or an involution.
  rcases (hmem x).mp hxI with h | h | h | h | h | h
  · rw [h]; simp
  · rw [h]; simp
  · rw [h, ← pow_two]; exact Subgroup.npow_mem_zpowers a 2
  · rw [h] at hxodd; rw [hb1o] at hxodd; exact absurd hxodd (by decide)
  · rw [h] at hxodd; rw [hb2o] at hxodd; exact absurd hxodd (by decide)
  · rw [h] at hxodd; rw [hc_ord] at hxodd; exact absurd hxodd (by decide)

end Work.CORE3
