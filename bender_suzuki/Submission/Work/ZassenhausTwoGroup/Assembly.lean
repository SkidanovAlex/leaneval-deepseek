import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.FeitInequality
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.count_le
import Submission.Work.ZassenhausTwoGroup.feitSection3_of
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Assembly: Feit's inequality from the §3 data

`FeitSection3Prop` (see `Submission.Work.ZassenhausTwoGroup.FeitThm2`) supplies, in the rank-one
Zassenhaus set-up with `Q` not a `2`-group, an irreducible character `χ₁` of `G` of degree
`q = |D|` together with `r = (q-1)/2` distinct irreducible characters `ηᵢ*` of degree
`m + 1 = |Q| + 1`, each a constituent of `χ₁χ̄₁`.  The final count of Feit's §3
(`count_le`, Feit (27)–(28)) then gives `m ≤ 2q + 1`, i.e. Feit's inequality
`|Q| - 1 ≤ 2|D|` — the content of `FeitInequalityProp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- **Feit's inequality (28) from the §3 character data.**  If the character-theoretic
conclusions of Feit's §3 hold in a finite simple group with rank-one Zassenhaus data in which
`Q` is not a `2`-group, then `|Q| - 1 ≤ 2|D|`. -/
theorem feitInequality_of_section3 (h3 : FeitSection3Prop) : FeitInequalityProp := by
  intro G _ hfin hsimple H Q t hsplit hz hnot
  classical
  let : Fintype G := Fintype.ofFinite G
  have hodd : Odd (Nat.card (twoPoint H t)) := odd_card_twoPoint hsplit.stronglyEmbedded hsplit.not_mem
  have hD : twoPoint H t ≠ ⊥ := twoPoint_ne_bot hsplit hz
  have hcard_ne_one : Nat.card (twoPoint H t) ≠ 1 := by
    intro h1
    exact hD (Subgroup.card_eq_one.mp h1)
  obtain ⟨χ, η, hχ, hdeg, hη, hηdeg, hinj, hcon⟩ := h3 G H Q t hsplit hz hnot
  have hqr : 2 * ((Nat.card (twoPoint H t) - 1) / 2) + 1 = Nat.card (twoPoint H t) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq : 1 < Nat.card (twoPoint H t) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcount := count_le hqr hq hχ hdeg hη hηdeg hinj hcon
  omega

/-- **`FeitInequalityProp` is now a theorem** (given Feit's Theorem 2 with its corollaries and
Thompson's theorem): the §3 data `FeitSection3Prop` is derived in-area by
`Work.ZassenhausTwoGroup.feitSection3_of` (Feit's (20), (18)/(19), (21)–(24) and (27) —
`zetaStar_norm`, `etaStar_data`, `chi1_degree_eq`, `bf35_chars`, `hchi_orb`), so only
`FeitThm2Prop` and `ThompsonFrobeniusProp` remain as inputs. -/
theorem feitInequality_of_thm2 (h2 : FeitThm2Prop) (hTh : ThompsonFrobeniusProp) :
    FeitInequalityProp :=
  feitInequality_of_section3 (feitSection3_of h2 hTh)

/-- The same conclusion, with the *named literature inputs* of the area (Feit's Theorem 2 with
its corollaries, and the Brauer–Fowler-based Lemmas 3.4/3.5) listed as hypotheses alongside the
§3 data: this is the form the final assembly of the paper should wire. -/
theorem feitInequality_of_literature (h2 : FeitThm2Prop) (hbf : BrauerFowlerProp)
    (h3 : FeitSection3Prop) : FeitInequalityProp :=
  feitInequality_of_section3 h3

end Work.ZassenhausTwoGroup
