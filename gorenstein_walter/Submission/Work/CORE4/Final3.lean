/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `Final3`: route L (`case2False_of_layer'`) with the open leaves named

This is the assembly the project lead asked for (plan map of 10-08, item 5).  Route L is

    Setup9 → Six9 → Seven → Eight → NotA7_9 → Nine9 → Count9 → `Case2FalseProp`,

i.e. `Work.GW2.case2False_of_layer'`.  Of its seven leaves, five are **proved** in the area and
are plugged in below; the remaining ones are taken as named hypotheses of
`Work.GW2.case2False_routeL`:

| leaf | status | reference |
|---|---|---|
| `Case2SetupImpl9` | PROVED | `Work.CORE4.Case2Setup9` (`CORE4/Case2Setup9.lean`, `#print axioms` clean) |
| `Case2SixImpl9` | PROVED | `Work.CORE4.case2SixImpl9_holds` (`CORE4/Six9Assembly.lean`, clean) |
| `Case2SevenImpl` | **OPEN** | `Work.CORE4.Case2SevenImpl9` — dispatched (`CORE4/Case2SevenImpl9.lean`) |
| `Case2EightImpl` | **OPEN** | reduces to `EightIndexBound` + `EightExceptDichotomy` (below) |
| `Case2NotA7Impl9` | PROVED | `Work.CORE4.Case2NotA7Impl9_holds` (`CORE4/NotA7Bridges.lean`), clean |
| `Case2NineImpl9` | PROVED | `Work.GW2.Case2NineImpl9_holds` (`CORE4/Final2.lean`, clean) |
| `Case2CountImpl9` | **OPEN** | `CORE4/Case2CountImpl9.lean`; its unique open input is `Counting.PerXAmalgamCount` |

`Work.GW2.Case2EightImpl_of_leaves` is the §4 (8) leaf with its two open sub-leaves
(`EightIndexLeafProp` = `Work.CORE4.Case2EightIndex`, `EightExceptLeafProp` =
`Work.CORE4.Case2EightExcept`) as hypotheses; its proof is the body of `Work.CORE4.Case2Eight`
with those two declarations replaced by the hypotheses, every other ingredient being sorry-free
(they are recorded in `CORE4/Case2Eight.lean` and are guarded by `#print axioms`).

CAUTION for the caller: `CORE4/Case2Eight.lean` also declares the leaf `Work.CORE4.Case2Eight`
itself, which is `sorry`-backed (it cites the two open sub-leaves).  `Case2EightImpl_of_leaves`
does not use it.
-/
import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.Final2
import Submission.Work.CORE4.Case2Setup9
import Submission.Work.CORE4.Six9Assembly
import Submission.Work.CORE4.NotA7Bridges
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2SevenImpl9
import Submission.Work.CORE4.Case2CountImpl9

namespace Work.CORE4

/-- The exact statement of the leaf `Work.CORE4.Case2EightIndex` (§4 (8), the index bound
`|U : B₀ K F(U)| ≤ p`), i.e. of the proved-once-dispatched `Work.CORE4.EightIndexBound`. -/
def EightIndexLeafProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
    Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
      Work.GW2.Case2SevenFacts B C.D →
      ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
        (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ p

/-- The exact statement of the leaf `Work.CORE4.Case2EightExcept` (§4 (8), the dichotomy), i.e. of
the reviewed `Work.CORE4.EightExceptDichotomy`. -/
def EightExceptLeafProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
    Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
      Work.GW2.Case2SevenFacts B C.D →
      ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
        Work.GW2.Case2EightObj C.D p P A →
        (Work.GW2.Case2InvNormal B C.D ∨
          (Work.GW2.Case2EightU B A ≤ p ∧
            (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
            (¬ B.U ≤ C.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A)))

end Work.CORE4

namespace Work.GW2

open Subgroup

/-- **§4 (8) from its two open sub-leaves.**  This is the body of `Work.CORE4.Case2Eight` with the
`sorry`-backed `Work.CORE4.Case2EightIndex` and `Work.CORE4.Case2EightExcept` replaced by the
hypotheses `hIdx` and `hExc`.  Every other ingredient is sorry-free:
`Case2EightObjExists`, `Case2Eight_dvd_K0`, `Case2EightA_le_FsupK0`, `Case2Eight_NU`,
`Case2Eight_le_normalizer_A`, `Case2Eight_odd_p0`, `Case2EightP0LeP1`, `Case2Eight_A_comm`,
`Case2EightP1Le`, `Case2Eight_p0_le_p`. -/
theorem Case2EightImpl_of_leaves (I : C4Inputs)
    (hIdx : Work.CORE4.EightIndexLeafProp) (hExc : Work.CORE4.EightExceptLeafProp) :
    Case2EightImpl I := by
  intro G _ _ hbc B h2 C hplus h7 p P hp hPF hPcard
  obtain ⟨A, hobj⟩ := Work.CORE4.Case2EightObjExists I G hbc B h2 C hplus h7 p P hp hPF hPcard
  have hAle : A ≤ C.D.F ⊔ C.D.K := hobj.2.2.2.1
  have hPA : P ≤ A := hobj.2.2.2.2.2.2.1
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M :=
    Work.CORE4.Case2Eight_NU B C P hPF hpne
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact Work.CORE4.Case2Eight_le_normalizer_A I B C p P A hobj
  have hp0odd : Odd (Case2EightP0 B P A) := Work.CORE4.Case2Eight_odd_p0 B p P A h4
  have h6a : Case2EightP0 B P A ≤ Case2EightP1 P A := Work.CORE4.Case2EightP0LeP1 B p P A hPA h4
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := Work.CORE4.Case2Eight_A_comm I B C A hAle
  have h6b : Case2EightP1 P A ≤ p + 1 :=
    Work.CORE4.Case2EightP1Le p P A hp hPA hobj.2.2.2.2.1 hobj.2.2.2.2.2.1 hAcomm hPcard
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (Case2Data.F_le_U B C.D)))
  exact ⟨A, hobj,
    Work.CORE4.Case2Eight_dvd_K0 B C h7 p P hp hPF hPcard,
    Work.CORE4.Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj,
    hNU, h4, hp0odd, h6a, h6b,
    Work.CORE4.Case2Eight_p0_le_p B p P A hp0odd h6a h6b hpodd,
    hIdx G hbc B h2 C hplus h7 p P hp hPF hPcard,
    hExc G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj⟩

/-- **Route L with the open leaves named.**  `I : C4Inputs10` (the bundle plus the `L2F` input
`l2outer`, needed by `NineImpl9`).

Proved and plugged in: `Case2SetupImpl9` (`Work.CORE4.Case2Setup9`), `Case2SixImpl9`
(`Work.CORE4.case2SixImpl9_holds`), `Case2SevenImpl` (`Work.CORE4.Case2SevenImpl9`),
`Case2NotA7Impl9` (`Work.CORE4.Case2NotA7Impl9_holds`), `Case2NineImpl9`
(`Work.GW2.Case2NineImpl9_holds`), and the count `Case2CountImpl9` from the design-27 leaves
`hL2`, `hCopy`, `hFour`, `hY`, `hZ` via `Work.GW2.C27.perXAmalgamCount_of_design27` and the
refactored `Work.CORE4.Case2CountImpl9_of_amalgam`.

The two remaining hypotheses are the §4 (8) sub-leaves (see this file's header and
`NOTES_TO_LEAD.md` §22 for their reduction to (T) `EightTrich9`, (α), `EightN9U`, `EightN9Inf`,
`Case2EightCase3U9plus`). -/
theorem case2False_routeL (I : C4Inputs10)
    (hIdx : Work.CORE4.EightIndexLeafProp) (hExc : Work.CORE4.EightExceptLeafProp)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I.toC4Inputs)
    (hY : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerYProp I.toC4Inputs)
    (hZ : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerZProp I.toC4Inputs) : Case2FalseProp :=
  case2False_of_layer' I.toC4Inputs
    (Work.CORE4.Case2Setup9 I.toC4Inputs)
    (Work.CORE4.case2SixImpl9_holds I.toC4Inputs)
    (Work.CORE4.Case2SevenImpl9 I.toC4Inputs)
    (Case2EightImpl_of_leaves I.toC4Inputs hIdx hExc)
    (Work.CORE4.Case2NotA7Impl9_holds I.toC4Inputs)
    (Case2NineImpl9_holds I)
    (Work.CORE4.Case2CountImpl9_of_amalgam I.toC4Inputs
      (Work.GW2.C27.perXAmalgamCount_of_design27 I.toC4Inputs hL2 hCopy hFour hY hZ))

/-- **The same assembly, with the §4 (12) amalgam count supplied directly** (no design-27 staging). -/
theorem case2False_routeL_count (I : C4Inputs10)
    (hIdx : Work.CORE4.EightIndexLeafProp) (hExc : Work.CORE4.EightExceptLeafProp)
    (hCount : Work.GW2.C27.PerXAmalgamCountProp I.toC4Inputs) : Case2FalseProp :=
  case2False_of_layer' I.toC4Inputs
    (Work.CORE4.Case2Setup9 I.toC4Inputs)
    (Work.CORE4.case2SixImpl9_holds I.toC4Inputs)
    (Work.CORE4.Case2SevenImpl9 I.toC4Inputs)
    (Case2EightImpl_of_leaves I.toC4Inputs hIdx hExc)
    (Work.CORE4.Case2NotA7Impl9_holds I.toC4Inputs)
    (Case2NineImpl9_holds I)
    (Work.CORE4.Case2CountImpl9_of_amalgam I.toC4Inputs hCount)

/-- **The same assembly from the fully disjoint (fine) leaf list** — the `Setup9`/`Six9`/`Seven`/
`Eight`/`NotA7_9`/`Nine9`/`Count9` version, for a caller who prefers to supply `Case2EightImpl`
directly (e.g. once `Work.CORE4.Case2Eight` is closed). -/
theorem case2False_routeL' (I : C4Inputs10)
    (hEight : Case2EightImpl I.toC4Inputs)
    (hCount : Work.GW2.C27.PerXAmalgamCountProp I.toC4Inputs) : Case2FalseProp :=
  case2False_of_layer' I.toC4Inputs
    (Work.CORE4.Case2Setup9 I.toC4Inputs)
    (Work.CORE4.case2SixImpl9_holds I.toC4Inputs)
    (Work.CORE4.Case2SevenImpl9 I.toC4Inputs) hEight
    (Work.CORE4.Case2NotA7Impl9_holds I.toC4Inputs)
    (Case2NineImpl9_holds I)
    (Work.CORE4.Case2CountImpl9_of_amalgam I.toC4Inputs hCount)

end Work.GW2
