import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Kahn.Nibble
import Submission.Work.Deep.Kahn.kahnCore_of_round
import Submission.Work.Deep.Kahn.kahnList_of_kahnCore
import Submission.Work.Deep.Kahn.kahnStatement_of_kahnList
import Submission.Work.Deep.Kahn.kahnRoundStatement

/-!
# Kahn's theorem (paper Theorem 4.6)

This is the entry point of the subproject `Work.Deep.Kahn`.  Importing this
module gives access to

* `Work.Deep.Kahn.kahnStatement : ErdosFaberLovaszConjecture.KahnStatement`
  (**the deliverable**: Kahn's asymptotically optimal list-edge-colouring
  theorem for linear hypergraphs, the paper's Theorem 4.6), proved in
  `Submission/Work/Deep/Kahn/kahnRoundStatement.lean` and dependent on no
  axioms beyond Lean's three standard ones (`propext`, `Classical.choice`,
  `Quot.sound`);
* the two proved reductions of the chapter:
  * `kahnStatement_of_kahnCore` — `KahnCoreStatement → KahnStatement`
    (list form for edges of size at least two implies the paper's form),
  * `kahnStatement_of_round` — `KahnRoundStatement → KahnStatement`
    (the one-round semi-random step implies the paper's form);
* the one-round interface `KahnRoundStatement` and the loss/degree vocabulary
  (`lostColours`, `lostColours_subset_of_palette`, …) in `Nibble.lean`.

## The architecture of the proof

(Kahn 1996, *Asymptotically good list-colourings*; the paper's Theorem 4.6.)

1. **Available lists.**  Forbidden lists `C e` of size `≤ αD/2` inside a colour
   set of size `c ≥ (1+α)D` give available lists `univ \ C e` of size
   `≥ (1+α/2)D` (`kahnStatement_of_kahnList`).
2. **Edges of size 0 and 1** are coloured greedily after the rest
   (`kahnList_of_kahnCore`, via the greedy bound
   `listColorable_of_card_gt_sum_degree`).
3. **The semi-random round** (the deep input, `KahnRoundStatement`): with `Δ = D`
   and lists of size `(1+β)D`, one round colours all but a `θ`-fraction of the
   edges at every vertex while an uncoloured edge loses at most `ψ(1+β)D`
   colours of its list, for `ψ < θ`.
4. **Iteration** (`kahnCore_of_round`): `D ↦ (1-θ)D` and `ℓ ↦ ℓ - ψ(1+β)D`, so
   the slack `(1-ψ)/(1-θ) > 1` grows geometrically and after a bounded number
   of rounds the residual hypergraph satisfies
   `∑_{v∈e} (d(v)-1) < |L e|`, where the greedy bound finishes.
5. The round itself is proved in `kahnRoundStatement.lean` by the colour-degree
   form of the nibble (regularised instance `nibbleRegularised`, regularisation
   `kahnEmbedding`, gluing `nibbleRoundGlue`, iteration
   `kahnCore_of_roundStepB`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- Kahn's theorem from its list form restricted to edges of size at least two
(uses only the two proven reductions `kahnList_of_kahnCore` and
`kahnStatement_of_kahnList`). -/
theorem kahnStatement_of_kahnCore (h : KahnCoreStatement) : KahnStatement :=
  kahnStatement_of_kahnList (kahnList_of_kahnCore h)

/-- **Kahn's theorem** (paper Theorem 4.6) from the one-round semi-random step
of the nibble, and its iteration. -/
theorem kahnStatement_of_round (h : KahnRoundStatement) : KahnStatement :=
  kahnStatement_of_kahnCore (kahnCore_of_round h)

/-- **Kahn's theorem** (paper Theorem 4.6) from the round that colours
everything: `KahnRoundStatement` is satisfied by `𝓗₀ := 𝓗`. -/
theorem kahnStatement_of_roundStatement (h : KahnRoundStatement) : KahnStatement :=
  kahnStatement_of_round h

end Work.Deep.Kahn
