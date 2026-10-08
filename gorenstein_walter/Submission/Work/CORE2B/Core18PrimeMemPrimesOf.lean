import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.C18PrimeMemPrimesOf_proved

/-!
# GW design 18, item A′, leaf H5: a nontrivial `p`-subgroup of `Y` puts `p` in `π(Y)`

Sketch (≤ 0.05k): `IsPGroup.card_eq_or_dvd`/`IsPGroup.ne_bot_iff`-style: `p ∣ |X|`, and
`|X| ∣ |Y|` (`Subgroup.card_dvd_of_le`); `primesOf Y = {q | q ∈ (Nat.card Y).primeFactors}`.
-/


namespace Work.GW18

open Subgroup

theorem Core18PrimeMemPrimesOf {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (X Y : Subgroup G) (hXY : X ≤ Y) (hX : X ≠ ⊥) (hXp : IsPGroup p X) :
    p ∈ Work.GW2.primesOf Y := Work.CORE2B.C18PrimeMemPrimesOf_proved p X Y hXY hX hXp

end Work.GW18
