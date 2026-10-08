/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the four `A₇`-chain leaves in bundled (`C15`) form

`Work.CORE4.notA7_of_four_leaves` (`Submission/Work/CORE4/NotA7Assembly.lean`) produces
`Case2NotA7Impl9` from the four bundled propositions
`Work.CORE4.C15.A7UMinusProp`, `…A7IndexHWeakProp`, `…A7CosetWeakProp`, `…A7SmallIndexWeakProp`.
The four leaf theorems proved in `Submission/Work/CORE4/NotA7/` are stated in unfolded form; this
file records that they have exactly the bundled types, so the assembly can consume them directly.
-/
import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.NotA7.A3UMinus
import Submission.Work.CORE4.NotA7.A5Weak
import Submission.Work.CORE4.NotA7.A6Weak
import Submission.Work.CORE4.NotA7.A7Weak
import Submission.Work.CORE4.NotA7Assembly

namespace Work.CORE4

/-- The leaf `A3m`/`A7UMinusProp` (`Submission/Work/CORE4/NotA7/A3UMinus.lean`), bundled. -/
theorem A7UMinusProp_holds (I : Work.GW2.C4Inputs) : C15.A7UMinusProp I :=
  NotA7.A3UMinus I

/-- The leaf `A5`/`A7IndexHWeakProp` (`Submission/Work/CORE4/NotA7/A5Weak.lean`), bundled. -/
theorem A7IndexHWeakProp_holds (I : Work.GW2.C4Inputs) : C15.A7IndexHWeakProp I :=
  NotA7.A5Weak I

/-- The leaf `A6`/`A7CosetWeakProp` (`Submission/Work/CORE4/NotA7/A6Weak.lean`), bundled. -/
theorem A7CosetWeakProp_holds (I : Work.GW2.C4Inputs) : C15.A7CosetWeakProp I :=
  NotA7.A6Weak I

/-- The leaf `A7`/`A7SmallIndexWeakProp` (`Submission/Work/CORE4/NotA7/A7Weak.lean`), bundled. -/
theorem A7SmallIndexWeakProp_holds (I : Work.GW2.C4Inputs) : C15.A7SmallIndexWeakProp I :=
  NotA7.A7Weak I

/-! ## The assembly: `Case2NotA7Impl9` fully discharged -/

/-- **The `A₇` chain is complete**: `Case2NotA7Impl9` (Bender §4, elimination of `E/Z(E) ≅ A₇`)
follows from the four now-proved leaves by `Work.CORE4.notA7_of_four_leaves`. -/
theorem Case2NotA7Impl9_holds (I : Work.GW2.C4Inputs) : Work.GW2.Case2NotA7Impl9 I :=
  notA7_of_four_leaves I (A7UMinusProp_holds I) (A7IndexHWeakProp_holds I)
    (A7CosetWeakProp_holds I) (A7SmallIndexWeakProp_holds I)

end Work.CORE4
