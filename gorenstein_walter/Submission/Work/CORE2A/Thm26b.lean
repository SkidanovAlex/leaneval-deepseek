/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: Theorem 2.6, step 2 — `E(Ĥ) = 1`

Bender 1981, p. 220: *"Next suppose `1 ≠ E := E(Ĥ)`. Then `SE/Z(E)` is some `PGL₂(q)`, again
by Lemma 2.1. … This proves `E(Ĥ) = 1`."*

The paragraph consists of two halves:

* the **structural** half (`Thm26bPGLProp`, proved as `Work.CORE2A.Thm26bPGL` from design pass 4,
  `_design_gw/Core4.lean` §2): if `E(Ĥ) ≠ 1` then `⟨S, E(Ĥ)⟩/Z(E(Ĥ)) ≅ PGL₂(q)`.
* the **counting/fusion** half (Bender's `t ∈ E`, the two commutator tori `R = [t, C_E(s)]`,
  `R* = [t, C_E(ts)]`, the involution `y` with `t^y = s ∉ E`, `8 ∣ |Ĥ ∩ Ĥ^y|`, and `y`
  centralizing an involution of `E`): all of it concludes that `Ĥ` has a single class of
  involutions, contradicting Lemma 2.1.

This file isolates the *conclusion* of that half as the leaf `Work.GW2.Thm26bOneClassProp` and
proves the assembly:

* `thm26b_of_oneClass : Lemma21Prop → Thm26bOneClassProp → Thm26bProp`.

`Thm26bOneClassProp` keeps the full `BenderCtx` binder on purpose: the *intermediate* claims of
the paragraph are not consequences of the local data alone (in `G = A₇`, `Ĥ = S₅`,
`E(Ĥ) = A₅` the local data hold, but `Ĥ` has two classes of involutions — the exclusion of that
model is precisely `BenderCtx.notA7`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- Theorem 2.6, step 2: `E(Ĥ) = 1`.  Assembly of Lemma 2.1 with Bender's paragraph, whose
conclusion is packaged as `Thm26bOneClassProp`. -/
theorem thm26b_of_oneClass (h21 : Work.GW2.Lemma21Prop) (hO : Work.GW2.Thm26bOneClassProp) :
    Work.GW2.Thm26bProp := by
  intro G _instG _instFin hFT hctx B
  by_contra hne
  exact h21 G hFT hctx B (hO G hFT hctx B hne)

end Work.CORE2A
