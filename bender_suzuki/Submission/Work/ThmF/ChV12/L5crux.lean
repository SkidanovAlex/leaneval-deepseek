import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.X5_rankOne_of
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5crux` — the single remaining gap of Ch. V §2 Lemma 5

**The gap, in its weakest known form:**

  `Q = Q0sub H` and `X5 H t = ⊤` force `centD H t = ⊥`,

for `Hyp5` data and `ChIIFourProp`.  Equivalently: *case a) of Peterfalvi II Ch. VI §1
(`Q = Q0sub H`) is incompatible with `V = centD H t ≠ 1` in a simple group.*

Why this is exactly what is missing (see `L5route.lean` for the proofs of everything else):

* the branch `V = ⊥` is `Ksub_eq_Kset_of_centD_bot` (App. I (1)(b));
* the branch `W = C_V(K) ≠ ⊥` is `Ksub_eq_Kset_of_W_ne_bot` (Ch. II §4 Prop. 3 (d));
* the branch `Q ≠ Q0sub H` is `Ksub_eq_Kset_of_Q_ne_Q0sub`, *proved without any extra input*:
  there `X5 H t ≠ ⊤` (because `X5 ⊓ Q = Q0sub H`), so `(B1)` from `Hyp5.sit` plus the model
  facts give `Ksub H t = Kset H t`;
* the branch `Q = Q0sub H` with `X5 H t ≠ ⊤` is the same argument;
* so only `Q = Q0sub H` with `X5 H t = ⊤` (hence `G = X5 H t`, a *simple* group) is left, and
  there the extra conclusion needed is exactly `V = ⊥`.

Two further remarks that locate the difficulty precisely.

1. In the remaining case `Q = Q0sub H`, `X5 H t = ⊤` one has `Ksub H t = D = twoPoint H t`
   (from `|X5| = |Q0sub|·|Ksub|·(1+|Q0sub|)` and `|G| = |Q|·|D|·(1+|Q|)`, both proved in
   `L5route.lean`), while `|Kset H t| = |Inv H| = |Q0sub H| - 1 < |D|` as soon as `V ≠ 1`.  So
   in that case the conclusion `Ksub = Kset` is *false*; consequently this file's statement is
   provable **iff** the target `Work.ThmF.ChV12.lemma5` is true.
2. The source proves the corresponding statement (Ch. V §1 Prop. 2) through Appendix X, applied
   to the faithful transitive action of `D/W` on `Q₀ = ⟨Inv H⟩`: the whole argument is
   formalised in `Work.ThmF.ChV12.Ksub_cyclic_normal`, whose only non-elementary input is the
   solvability of the odd-order group `D/W`, i.e. Feit–Thompson (`Work.Skeleton.minSimpleOdd_false`
   is the single hole of the workspace's FT library).  The `hyp5`-only form of Prop. 2 is
   isolated in `Submission/Work/PSU3/StageA/Ksub_eq_Kset_of_W_bot.lean`.
   A Feit–Thompson-free proof would have to establish the classical sharp-transitivity fact
   used there: a subset `K` of `GL(n,2)` of size `2ⁿ - 1` acting sharply transitively on the
   non-zero vectors is closed under multiplication (the "near-field multiplication" it defines
   is associative; for characteristic `2` all finite near-fields are fields — Zassenhaus 1936).
3. Computationally the statement is comfortably true in all checked instances: exhaustive GAP
   searches over all `(G,H,t)` whose data satisfy the consequences of `ChIIFourProp`
   (involutions of `H` commute, `|Q0sub H| = |Inv H| + 1` a power of two, `Kset` sharply
   transitive on `Inv H`) found no counterexample up to order `150`, and each of the models
   (`PSL(2,q)`, `Sz(q)`, `PSU(3,q)`, `PΓL(2,8)`) satisfies it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

/- NOTE: **The remaining gap.**  Case a) of Ch. VI §1 forces (in the `X5 = ⊤` situation) `V = 1`.

Status 2026-10-05: open.  The declaration `L5crux` was requested here and the prover returned it
as *mis-stated*: the statement needs Ch. VI §1's case analysis and §2 Lemma 4, neither available.
It is recorded as an open input of the area (see `NOTES.md`) and is stated below as the named
`Prop` `L5cruxProp`, which `L5route` takes as a hypothesis.  The module is kept because
`L5cruxAux`/`L5route` import it. -/

/-- **The remaining gap of Ch. V §1 Prop. 2** (case `V ≠ 1`, `W = 1`, `Q = Q₀`): then either
`X5 H t ≠ ⊤` or `V = centD H t = ⊥`.  This is the shape of the one case the `ChIIFourProp` route
does not reach; see the note above. -/
def L5cruxProp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G},
    Submission.Blueprint.ChIIFourProp → Work.ThmF.Lemma5.Hyp5 H Q t s →
    Q = Work.ThmF.Q0sub H →
    (Work.ThmF.Lemma5.X5 H t ≠ ⊤ ∨ Submission.Blueprint.centD H t = ⊥)

end Work.ThmF.ChV12
