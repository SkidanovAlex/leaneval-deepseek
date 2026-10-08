import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|O_2(Q)|` and `|O_{2'}(Q)|` are coprime

For any subgroup `Q` of a finite group `G` the orders of the `2`-core and the `2'`-core of `Q`
are coprime:

  `Nat.Coprime |twoPart Q| |oddPart Q|`,  where `twoPart Q = O_2(Q)`, `oddPart Q = O_{2'}(Q)`.

The mathematical content is one line: `O_2(Q)` is a `2`-group (`Work.Fitting.piCore_isPiNat`
for the predicate `π = (· = 2)`), so every prime divisor of `|twoPart Q|` equals `2`, while
`O_{2'}(Q)` is a `2'`-group (`π = (· ≠ 2)`), so no prime divisor of `|oddPart Q|` equals `2`.
A common prime divisor would have to be both `2` and not `2`.  `Nat.coprime_of_dvd` turns this
"no common prime" statement into the coprimality of the two cardinals.

Note that *nilpotency* of `Q` is not used: this holds for every finite subgroup, and indeed
`twoPart Q` and `oddPart Q` are the images of the two cores of `Q` along the (injective)
inclusion `Q.subtype`, so the cardinalities may be computed inside `Q`.
-/

namespace Work.ZassenhausTwoGroup

/-- `|O_2(Q)| = |O_2(↥Q)|`: `twoPart Q` is the image of the `2`-core of `Q` along the injective
inclusion `Q.subtype`, and an injective map preserves cardinalities. -/
theorem card_twoPart {G : Type} [Group G] {Q : Subgroup G} :
    Nat.card (twoPart Q) = Nat.card (Work.Fitting.pCore 2 ↥Q) := by
  rw [twoPart]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)

/-- `|O_{2'}(Q)| = |O_{2'}(↥Q)|`: `oddPart Q` is the image of the `2'`-core of `Q` along the
injective inclusion `Q.subtype`. -/
theorem card_oddPart {G : Type} [Group G] {Q : Subgroup G} :
    Nat.card (oddPart Q) = Nat.card (Work.Fitting.pPrimeCore 2 ↥Q) := by
  rw [oddPart]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)

/-- The `2`-part and the odd part of a finite subgroup have coprime orders: `O_2(Q)` is a
`2`-group and `O_{2'}(Q)` is a `2'`-group, so no prime divides both orders. -/
theorem coprime_twoPart_oddPart {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    Nat.Coprime (Nat.card (Work.ZassenhausTwoGroup.twoPart Q))
      (Nat.card (Work.ZassenhausTwoGroup.oddPart Q)) := by
  rw [card_twoPart (Q := Q), card_oddPart (Q := Q)]
  -- A prime dividing the `2`-core must be `2`, a prime dividing the `2'`-core must not be `2`.
  refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
  exact (Work.Fitting.piCore_isPiNat ↥Q (fun q => q ≠ 2)) p hp hpn
    ((Work.Fitting.piCore_isPiNat ↥Q (fun q => q = 2)) p hp hpm)

end Work.ZassenhausTwoGroup
