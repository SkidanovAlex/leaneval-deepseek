import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Chain` — the standing open input of Ch. V §3

Peterfalvi II Ch. V §3 proves Théorème F by contradiction: under the standing context (B0)–(B2),
`G` simple, split rank-one data `H = Q ⋊ D`, the structure identity `t s t = r⁻¹ t r` and
hypothesis

* **(F1)** some `P ≤ V = C_D(t)` of prime order has `C_G(P)` of 2-rank `1`,

the numbered steps (1)–(17) of pp. 248–256 end in a contradiction (a normal subgroup of index
`p`, contradicting (F2), which is automatic for simple `G`).

This module records the **whole §3 contradiction as one named `Prop`**, `ChV3Prop`, so that the
area can be used before the chain is finished: `Work.ThmF.ThmF` is a theorem from `ChV3Prop` (plus
the other areas' `Prop`s and the four literature inputs §3 quotes).  The individual steps are
built under `Submission/Work/ThmF/ChV3/` (`step1`, `step3`, …, `A_reduction`, `D_nonabelian`,
`step6aux_count`), each carrying the proved preliminaries of its argument; the targets themselves
are stated and dispatched from here.

The four literature inputs threaded through `ChV3Prop` are the ones `Tools/External.lean` records:
Wielandt's fixed-point formula (HB XI 12.4), Hall–Wielandt (M. Hall §14.4), HB IX (2-7), and the
near-field shadow of App. XI (`ChV3/NearField.lean`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Submission.Blueprint

/-- **The open content of Ch. V §3**: the context `CtxF H Q t s r P` is contradictory (steps
(1)–(17) of Peterfalvi II pp. 248–256), given the other areas' `Prop`s used by §1–§2 and the four
literature inputs §3 quotes. -/
def ChV3Prop : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G},
    FeitThompsonProp → ChIIFourProp → ThompsonFrobeniusProp →
    Work.ThmF.WielandtFixedPoint → Work.ThmF.HallWielandtProp →
    Work.ThmF.ArithmeticNineTwoSeven → NearFieldAppXIProp →
    CtxF H Q t s r P → False

end Work.ThmF.ChV3
