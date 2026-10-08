/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: assembly of the Brauer–Suzuki–Wall theorem

This file assembles the intermediate contracts of `Submission/Work/BSW/Concl.lean` into

```
Work.BSW.bswZass2_of_cases : BSWK2Prop → BSWK4Prop → BSWGt4Prop → BSWZass2Prop
```

and then composes the area's own `BSWZass2Prop` with the Zassenhaus recognition step
`Work.GW2.ZassOdd2Prop` of area ZASS into the area's deliverable

```
Work.BSW.bsw2 : BSWZass2Prop → ZassOdd2Prop → BSW2Prop
work.GW2.bsw2  (alias)
```

Callers (areas `CORE2A`, `CORE2B`) should import this module and use `Work.GW2.bsw2`.
-/
import Submission.Work.BSW.Concl

open scoped MatrixGroups

namespace Work.BSW

open Subgroup Work.GW2

section Assembly

/-- The `|K| = 2` case from its two parts. -/
theorem bswK2Prop_of_parts (h1 : BSWK2OrderProp) (h2 : BSWK2StructureProp) : BSWK2Prop := by
  intro G _ _ hS hnab t s K h hk
  exact h2 G hS hnab t s K h hk (h1 G hS hnab t s K h hk)

/-- The `|K| = 4` case from its two parts. -/
theorem bswK4Prop_of_parts (h1 : BSWK4OrderProp) (h2 : BSWK4StructureProp) : BSWK4Prop := by
  intro G _ _ hS hnab t s K h hk
  exact h2 G hS hnab t s K h hk (h1 G hS hnab t s K h hk)

/-- The `|K| > 4` case from its two parts. -/
theorem bswGt4Prop_of_parts (h1 : BSWOrderProp) (h2 : BSWCompletionProp) : BSWGt4Prop := by
  intro G _ _ hS hnab t s K h hk
  exact h2 G hS hnab t s K h hk (h1 G hS hnab t s K h hk)

/-- **Bender's case analysis.** With `BSWParityProp` (`|K|` is even and `|K| ≥ 2`) the three cases
`|K| = 2`, `|K| = 4`, `|K| > 4` cover every configuration satisfying `BSWHyps2`; each of them
produces Bender's conclusion (1)–(4) (`IsBSWData`), which `BSWDataZassProp` converts into the
Zassenhaus action. -/
theorem bswZass2_of_cases (hpar : BSWParityProp) (h2 : BSWK2Prop) (h4 : BSWK4Prop)
    (hgt : BSWGt4Prop) (hdata : BSWDataZassProp) : BSWZass2Prop := by
  intro G _ _ hS hnab t s K h
  have hk0 : Nat.card ↥K ≠ 0 := by
    haveI : Fintype ↥K := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  obtain ⟨m, hm⟩ := hpar G t s K h
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by omega) hk0
    · exact h0
  rcases lt_or_ge m 3 with h3 | h3
  · interval_cases m
    · exact hdata G hS hnab 5 (h2 G hS hnab t s K h (by omega))
    · rcases h4 G hS hnab t s K h (by omega) with h7 | h9
      · exact hdata G hS hnab 7 h7
      · exact hdata G hS hnab 9 h9
  · obtain ⟨q, _, hq⟩ := hgt G hS hnab t s K h (by omega)
    exact hdata G hS hnab q hq

end Assembly

/-! ## The deliverable -/

/-- **The deliverable of area BSW**: the Brauer–Suzuki–Wall recognition step
`Work.GW2.BSW2Prop` follows from the area's own `BSWZass2Prop` (Bender 1974) composed with the
Zassenhaus recognition step `Work.GW2.ZassOdd2Prop` of area ZASS (HB III XI 1.11–1.12).

A caller obtains `BSW2Prop` from the two area theorems; the `ZassConcl` action produced by
`BSWZass2Prop` is fed to `ZassOdd2Prop` verbatim. -/
theorem bsw2 (hBZ : BSWZass2Prop) (hZ : ZassOdd2Prop) : BSW2Prop := by
  intro G _ _ hS hnab t s K h
  obtain ⟨p, k, hfact, hodd, h5, M, hz⟩ := hBZ G hS hnab t s K h
  haveI : Fact p.Prime := hfact
  exact ⟨p, k, hfact, hodd, h5, hZ G (G ⧸ M) p k hodd h5 hS hz⟩

end Work.BSW

namespace Work.GW2

/-- Alias of `Work.BSW.bsw2` in the contract namespace. -/
theorem bsw2 (hBZ : BSWZass2Prop) (hZ : ZassOdd2Prop) : BSW2Prop := Work.BSW.bsw2 hBZ hZ

end Work.GW2
