import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API

/-!
# The call-site hypotheses of Bender 1981, Lemma 2.9 (corrected leaf `L29_contra_h27`)

`L29_contra` (see `Basic.lean`) takes only `L29Hyp B V N`.  At every call site in Bender's paper
(p. 221–223: Theorem 2.10 and §3, "Take a maximal subgroup `M` of `G` containing `N_G(P₁)`.
Then `S ≤ M` …") the subgroup `N` is in fact a **maximal** subgroup with `Ĥ ⇝ N`, `N ≄ Ĥ` and
`S ≤ N`.  Exactly as the sibling restatements `L27_su_not_le_h22` and `L28_S0U_ne_bot_h26` added
the inputs `Lemma22Prop` resp. `Thm26Prop`, the corrected Lemma 2.9 leaf takes the §2 inputs and
the call-site data.

This file contains only definitions (no proofs), so it is `sorry`-free and can be imported by any
prover working on the corrected leaf or its pieces.
-/

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-- **The hypotheses of the corrected Lemma 2.9 leaf.** `L29Hyp B V N` together with the data
available at the call sites: `N` maximal, `Ĥ ⇝ N`, `¬ N ≤ Ĥ`, and `S ≤ N`. -/
structure L29CallSite (B : Work.GW2.BenderSetup G) (V N : Subgroup G) : Prop where
  hyp : L29Hyp B V N
  coatom : IsCoatom N
  rel : Work.GW2.BRel B.Hhat N
  not_le : ¬ N ≤ B.Hhat
  S_le_N : (B.S : Subgroup G) ≤ N

/-- **Corrected leaf `L29`**: `L29_contra` with the call-site hypotheses `L29CallSite` and the §2
inputs `h22 : Lemma22Prop`, `h26 : Thm26Prop`, `h27 : Lemma27Prop` of the paper — the same kind of
correction the sibling leaves received (`L27_su_not_le_h22`, `L28_S0U_ne_bot_h26`). -/
def L29_contra_h27 : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop) (_h26 : Work.GW2.Thm26Prop)
    (_h27 : Work.GW2.Lemma27Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (V N : Subgroup G), L29CallSite B V N →
      V ⊓ Work.GW2.pCoreIn 2 N = ⊥ → V ⊓ Work.GW2.layerIn N = ⊥ → False

end Work.CORE2B
