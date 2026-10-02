import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.RoundDefs

/-!
# The one-round nibble: auxiliary vocabulary for the regularised analysis

This module fixes the auxiliary random variables of the *regularised* one-round
analysis (`Work.Deep.Kahn.RegularisedNibbleStatement`), so that the probabilistic
estimates can be stated in the requester's own vocabulary.

## The round outcome

`Round.Space K 𝓗 L = ∀ e : 𝓗, Fin K × Fin (L e).card` is the outcome space of the
round: every edge independently draws an *activation class* in `Fin K` and an
index into its own list.  `Round.kept ω e` (edge `e` is activated and no other
activated edge meeting it carries the same colour) and `Round.colour ω e`
(the colour of `e`) are as in `RoundDefs`.

We write `𝓗₀ := Round.keptSub ω` for the kept subhypergraph and
`φ := Round.keptColoring ω` for the induced proper list-colouring of `𝓗₀`.

## The quantities of the colour-degree estimate

Fix a vertex `x` and a colour `γ`.  The colour degree of the pair `(x,γ)` after the
round is bounded by the number of *uncoloured* edges `e ∋ x` whose residual list can
still contain `γ`.  Writing `usedColours ω e` for the colours used by the kept edges
meeting `e`, that number is at most `D - keptCount - usedCount` where

* `keptCount ω x γ = #{e ∋ x : e ∈ 𝓗₀, γ ∈ L e}` — the edges through `x` carrying `γ`
  that were **coloured** in the round (these can no longer be counted), and
* `usedCount ω x γ = #{e ∋ x : e ∉ 𝓗₀, γ ∈ usedColours ω e}` — the uncoloured edges
  through `x` carrying `γ` at which `γ` was **used** by a kept edge meeting them.

Both mechanisms are needed: the first contributes only `≈ pD`, while the second
contributes `≈ Dα` with `α = C(D-1)p/Λ`; the second is *localised* (spread over the
edges instead of all-or-nothing) which is what makes the colour-degree estimate
concentrate.  (Using the residual list itself, i.e. `Round.residual`, gives a
quantity whose distribution is bimodal: on the event "no edge through `x` is
activated with colour `γ`" — which has probability `≈ 1` — every one of the `D`
edges of `E(x,γ)` loses `γ` only if it happens to meet a `γ`-activated edge through
one of its *other* vertices, giving a count of `≈ D(1-p-α/C)` which exceeds
`newDeg + ηD` whenever `η < α/C`.  So `L'` must be allowed to *contain* lost colours,
not just subsets of the residual.)
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

/-- The colours **used at the edge `e`** by the round `ω`: the colours of the kept
edges meeting `e`.  These are precisely the colours that the list of `e` may no
longer contain. -/
def usedColours {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : Finset (Fin c) := by
  classical
  exact (Finset.univ.filter (fun f : 𝓗 => kept ω f ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)).image (fun f => colour ω f)

/-- The number of edges through `x` carrying the colour `γ` that were coloured in
the round: the "`pD` term" of the colour-degree estimate. -/
def keptCount {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => kept ω e ∧ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e)).card

/-- The number of *uncoloured* edges through `x` carrying the colour `γ` at which
`γ` is used by a kept edge meeting them: the "`Dα` term" of the colour-degree
estimate. -/
def usedCount {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧
    γ ∈ L e ∧ γ ∈ usedColours ω e)).card

/-- The number of uncoloured edges through `x` on which the colour `γ` is still
available after the round, i.e. that carry `γ` in their list and do not use `γ` at
a vertex. -/
def residualCount {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧
    γ ∈ L e ∧ γ ∉ usedColours ω e)).card

end Round

end

end Work.Deep.Kahn
