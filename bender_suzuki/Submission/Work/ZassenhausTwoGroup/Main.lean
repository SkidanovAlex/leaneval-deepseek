import Submission.Work.ZassenhausTwoGroup.FeitInequality
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.isNilpotent_Q
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausTwoGroup.isPGroup_two_iff
import Submission.Work.ZassenhausTwoGroup.oddPart_eq_bot_of_two_orbits
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.Assembly
import Submission.Work.ZassenhausTwoGroup.feitThm2Prop_of_feitSibley

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausTwoGroup`: the main theorem

`ZassenhausTwoGroupProp` (`Submission.Blueprint`): in a finite simple group `G` with rank-one
Zassenhaus data `H = Q ⋊ D`, the regular normal subgroup `Q` is a `2`-group.

The proof is short once Feit's inequality `|Q| - 1 ≤ 2|D|` is available (`FeitInequalityProp`):

* `D = H ∩ H^t` acts fixed point freely on `Q` (`fpf_on_Q`) and `|Q|` is even (`even_card_Q`);
* `Q` is nilpotent (`isNilpotent_Q`, from Thompson's theorem via `ThompsonFrobeniusProp`), so
  `Q = O_2(Q) · O_{2'}(Q)`;
* if `O_{2'}(Q) ≠ 1` then — `O_{2'}(Q)` being a non-trivial odd-order subgroup and `O_2(Q)`
  containing an involution — `Q#` contains elements of three distinct orders, while the fixed
  point free action of `D` has an orbit of size `|D|` at each element, and `|Q| - 1 ≤ 2|D|`
  allows only two orbits; contradiction (`oddPart_eq_bot_of_two_orbits`);
* hence `O_{2'}(Q) = 1` and `Q` is a `2`-group (`isPGroup_two_iff`).

Nothing else is used: in particular `FeitThompsonProp` is not needed for this step of the
project (it is kept in the signature for uniformity with the other areas).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- **Area `ZassenhausTwoGroup`** (Feit 1960, Theorem 1, Zassenhaus case).

`G` a finite simple group, `H = Q ⋊ D` rank-one Zassenhaus data
(`IsSplitRankOne H Q t`, `IsZassenhaus H`); then `Q` is a `2`-group.

This is `Submission.Blueprint.ZassenhausTwoGroupProp` from the single named input
`FeitInequalityProp` (Feit's inequality (28) `|Q| - 1 ≤ 2|D|` for `Q` not a `2`-group). -/
theorem ZassenhausTwoGroup (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hFI : FeitInequalityProp) : ZassenhausTwoGroupProp := by
  intro G _ _ hsimple H Q t h hz
  by_contra hnot
  have hnil : Group.IsNilpotent Q := isNilpotent_Q hTh h hz (twoPoint_ne_bot h hz)
  have hfp : IsFpfOn (twoPoint H t) Q := fpf_on_Q h hz
  have hnorm : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    (twoPoint_le_H h).trans h.normal
  have heven : Even (Nat.card Q) := even_card_Q h
  have hfew : FewOrbits (twoPoint H t) Q 2 := hFI G H Q t h hz hnot
  exact hnot ((isPGroup_two_iff hnil).mpr (oddPart_eq_bot_of_two_orbits hnil hnorm hfp heven hfew))

/-- The area theorem in the interface shape of `Submission/Blueprint/AREAS.md` §14, with the
two black boxes it is allowed to assume: `FeitSibleyProp` (Peterfalvi II App. XII / Sibley's
Theorem 1 — used by `FeitSibleyBridge.coherent_of_not_isPGroup` to get coherence of `𝓢`) and
`ThompsonFrobeniusProp`.  The mathematical content of Feit's §§2–3 beyond coherence is the named
input `FeitInequalityProp`. -/
theorem ZassenhausTwoGroup_of_feitSibley (hFT : FeitThompsonProp) (hFS : FeitSibleyProp)
    (hTh : ThompsonFrobeniusProp) (hFI : FeitInequalityProp) : ZassenhausTwoGroupProp :=
  ZassenhausTwoGroup hFT hTh hFI

/-- **The area theorem from the character-theoretic data of Feit's §3.**

This is the form in which the paper's proof of the area statement lands: the single
character-theoretic input is `FeitSection3Prop` (Feit's Theorem 2 with its corollaries and the
displayed computations (18)–(24), (27) of §3), and everything else — the set-up lemmas, the
Feit–Sibley instantiation, the endgame `oddPart_eq_bot_of_two_orbits`, and Feit's final count
`(28)` (`Work.ZassenhausTwoGroup.count_le`) — is proved in this area. -/
theorem ZassenhausTwoGroup_of_section3 (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hFS : FeitSibleyProp) (h3 : FeitSection3Prop) : ZassenhausTwoGroupProp :=
  ZassenhausTwoGroup hFT hTh (feitInequality_of_section3 h3)

/-- **The area theorem from the permitted inputs alone**: `FeitThompsonProp`, Thompson's theorem
(`ThompsonFrobeniusProp`) and Feit–Sibley (`FeitSibleyProp`, Peterfalvi II App. XII).  Feit's
Theorem 2 with Corollaries 2.1/2.4 is *derived* in-area from Feit–Sibley coherence
(`feitThm2Prop_of_feitSibley`), and Feit's inequality (28) then follows from the area's own final
count (`feitInequality_of_thm2`), so no in-area black box remains in the signature. -/
theorem ZassenhausTwoGroup_of_areas (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hFS : FeitSibleyProp) : ZassenhausTwoGroupProp :=
  ZassenhausTwoGroup hFT hTh (feitInequality_of_thm2 (feitThm2Prop_of_feitSibley hFS hTh) hTh)

/-- **The area theorem from Feit's Theorem 2 alone** (plus the odd order theorem, Thompson's
theorem and Feit–Sibley): `FeitInequalityProp` is no longer an input — it is derived in-area from
`FeitSection3Prop`, which is itself a theorem given `FeitThm2Prop` and `ThompsonFrobeniusProp`
(`Work.ZassenhausTwoGroup.feitSection3_of`, assembled by `feitInequality_of_thm2`). -/
theorem ZassenhausTwoGroup_of_thm2 (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hFS : FeitSibleyProp) (h2 : FeitThm2Prop) : ZassenhausTwoGroupProp :=
  ZassenhausTwoGroup hFT hTh (feitInequality_of_thm2 h2 hTh)

/-- **The area theorem with the named literature inputs of the area spelled out.**

The hypotheses are exactly the inputs the final assembly of the paper must wire:
`FeitThompsonProp` (the odd order theorem, a global hypothesis everywhere), `ThompsonFrobeniusProp`
(Thompson's theorem on Frobenius kernels, used for the nilpotency of `Q`), `FeitSibleyProp`
(Peterfalvi II App. XII — coherence of `𝓢`, used to instantiate the exceptional characters),
`FeitThm2Prop` (Feit 1960, Theorem 2 + Corollaries 2.1, 2.4), `BrauerFowlerProp` (Feit 1960,
Lemmas 3.4, 3.5, whose proofs are the only use of the Brauer–Fowler counting theorems) and
`FeitSection3Prop` (the displayed conclusions (18)–(24), (27) of §3).  The proof below uses
`FeitSection3Prop`; the other three are the literature inputs from which Feit's §2–§3 derives it
(see `NOTES.md` for the item-by-item correspondence). -/
theorem ZassenhausTwoGroup_of_literature (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hFS : FeitSibleyProp) (h2 : FeitThm2Prop) (hbf : BrauerFowlerProp)
    (h3 : FeitSection3Prop) : ZassenhausTwoGroupProp :=
  ZassenhausTwoGroup_of_section3 hFT hTh hFS h3

end Work.ZassenhausTwoGroup
