import Submission.Work.CORE3.Defs

/-!
# CORE3: the `A7RecProp` → `A7Rec2Prop` bridge

Design pass 4 (`Submission/Work/_design_gw/Core4.lean` §3) amends the `A₇` recognition contract to
`A7Rec2Prop` = `A7RecProp` + the minimal-counterexample premise `SmallerDGroups G`, which CORE3
has from `BenderCtx.ih`.

The old contract `Work.GW2.A7RecProp` (verbatim from `Contracts2.lean`) *implies* the amended one:
`A7RecHyps` contains `IsSimpleGroup G` and `Nat.card G = 2520` and all the other clauses of
`A7RecProp`'s hypothesis list, and the extra premise `SmallerDGroups G` is simply discarded.
So a caller holding the old `A7RecProp` (as in the lead's original assembly signature) can still
feed CORE3.
-/

namespace Work.CORE3

open Work.GW2

/-- The amended `A₇` contract follows from the original one. -/
theorem a7Rec2Prop_of_a7RecProp (h : A7RecProp) : Work.A7REC.A7Rec2Prop := by
  intro G hG hFin S z U V hY _hSmall
  obtain ⟨hS, hcard, hdih, hz, hzord, hzcen, hcen, hU, hUn, hV, hVfour, hg, hNUV, hNU⟩ := hY
  exact h G hS hcard S hdih z U V hz hzord hzcen hcen hU hUn hV hVfour hg hNUV hNU

end Work.CORE3
