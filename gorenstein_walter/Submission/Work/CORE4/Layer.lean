/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — assembly over the design-pass-9 layer

`Assembly.lean` composes the *old* fine split (Setup, Six, NotA7, Nine, Count) to `Case2FalseProp`.
This file composes the design-pass-9 split of `NOTES_LEAD_gw_design9.md` §1 / `Core9.lean`:

    Setup9 → Six9 → Seven (§4 (7)) → Eight (§4 (8)) → NotA7_9 → Nine9 → Count9 → contradiction,

where `Case2PrePlus` (Bender's Sylow condition `S ∩ M ∈ Syl₂(M)` and (1),(2)) is carried alongside
`Case2Pre` by every leaf, and `Case2SevenFacts` / `Case2EightAll` are the §4 (7)/(8) object layer.

`case2False_of_layer` is copied verbatim from `_design_gw/Core9.lean` §5 (with `Case2ArithProp` as
a hypothesis); `case2False_of_layer'` instantiates it with the proved `Work.GW2.case2Arith`.
-/
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Arith

namespace Work.GW2

open Subgroup

/-- `Case2FalseProp` from the restated split: Setup9, Six9, Seven, Eight, NotA7_9, Nine9 and
Count9, plus the arithmetic. -/
theorem case2False_of_layer (I : C4Inputs) (hArith : Case2ArithProp)
    (hSetup : Case2SetupImpl9 I) (hSix : Case2SixImpl9 I) (hSeven : Case2SevenImpl I)
    (hEight : Case2EightImpl I) (hNotA7 : Case2NotA7Impl9 I) (hNine : Case2NineImpl9 I)
    (hCount : Case2CountImpl9 I) : Case2FalseProp := by
  intro G _ _ _ hbc B h2
  obtain ⟨B', -, h2', D, hpre, hplus⟩ := hSetup G hbc B h2
  obtain ⟨hti, hcyc⟩ := hSix G hbc B' D hpre hplus
  let C : Case2Ctx6 B' := ⟨D, hpre, hti, hcyc⟩
  have h7 : Case2SevenFacts B' D := hSeven G hbc B' h2' C hplus
  have h8 : Case2EightAll B' D := hEight G hbc B' h2' C hplus h7
  have hA7 := hNotA7 G hbc B' h2' C hplus h7 h8
  have h9 := hNine G hbc B' h2' C hplus h7 h8 hA7
  let X : Case2Ctx B' := ⟨D, hpre, hti, hcyc, hA7, h9⟩
  obtain ⟨q, k, k', p, p0, p1, u, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13,
    e14⟩ := hCount G hbc B' h2' X hplus h7 h8
  exact hArith q k k' p p0 p1 u e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14

/-- `case2False_of_layer` with the arithmetic discharged by the proved `case2Arith`. -/
theorem case2False_of_layer' (I : C4Inputs)
    (hSetup : Case2SetupImpl9 I) (hSix : Case2SixImpl9 I) (hSeven : Case2SevenImpl I)
    (hEight : Case2EightImpl I) (hNotA7 : Case2NotA7Impl9 I) (hNine : Case2NineImpl9 I)
    (hCount : Case2CountImpl9 I) : Case2FalseProp :=
  case2False_of_layer I case2Arith hSetup hSix hSeven hEight hNotA7 hNine hCount

/-- The merged leaf `Case2TailImpl` (in flight) still follows from the fine split, as long as its
caller can supply `Case2PrePlus`.  Copied verbatim from `Core9.lean` §5. -/
theorem case2Tail_of_layer (I : C4Inputs) (hSeven : Case2SevenImpl I)
    (hEight : Case2EightImpl I) (hNotA7 : Case2NotA7Impl9 I) (hNine : Case2NineImpl9 I)
    (hCount : Case2CountImpl9 I) :
    ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
      ∀ C : Case2Ctx6 B, Case2PrePlus B C.D →
      ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
        ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
        p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧
        1 ≤ u ∧ u ≤ p ∧
        (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
            (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
          6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3) := by
  intro G _ _ hbc B h2 C hplus
  have h7 := hSeven G hbc B h2 C hplus
  have h8 := hEight G hbc B h2 C hplus h7
  have hA7 := hNotA7 G hbc B h2 C hplus h7 h8
  have h9 := hNine G hbc B h2 C hplus h7 h8 hA7
  exact hCount G hbc B h2 ⟨C.D, C.pre, C.F_ti, C.F_cyclic, hA7, h9⟩ hplus h7 h8

end Work.GW2
