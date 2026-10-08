import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.twoPart_sup_oddPart

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Q` is a `2`-group iff its odd part is trivial

For a finite nilpotent subgroup `Q ≤ G`, the odd part `oddPart Q = O_{2'}(Q)` is trivial exactly
when `Q` is a `2`-group.

* (⇒) If `Q` is a `2`-group then `|Q| = 2 ^ n`.  The `2'`-core `O_{2'}(Q)` is a `2'`-group
  (`Work.Fitting.piCore_isPiNat`), so its order is a divisor of `2 ^ n` all of whose prime
  divisors are different from `2`; hence `|O_{2'}(Q)| = 1` and `O_{2'}(Q) = ⊥`.
* (⇐) If `O_{2'}(Q) = ⊥` then, `Q` being nilpotent, `Q = O_2(Q) · O_{2'}(Q) = O_2(Q)`
  (`twoPart_sup_oddPart`).  The `2`-core of a finite group has order a power of `2`
  (`Work.Fitting.piCore_isPiNat` again), and passing to the image under the injective map
  `Q.subtype` does not change the order, so `|Q| = 2 ^ k` and `Q` is a `2`-group.

Nothing beyond the two `π`-core facts and elementary cardinal arithmetic is used.
-/

namespace Work.ZassenhausTwoGroup

/-- For `H ≤ Q ≤ G`, the image of `H` in `G` under `Q.subtype` is trivial iff `H` is. -/
private theorem map_subtype_eq_bot_iff {G : Type} [Group G] {Q : Subgroup G}
    {H : Subgroup ↥Q} : H.map Q.subtype = ⊥ ↔ H = ⊥ := by
  have hker : Q.subtype.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff Q.subtype).mpr (Subgroup.subtype_injective Q)
  rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff]

theorem isPGroup_two_iff {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (h : Group.IsNilpotent Q) :
    IsPGroup 2 Q ↔ Work.ZassenhausTwoGroup.oddPart Q = ⊥ := by
  constructor
  · intro hQ
    -- `Q` is a `2`-group, so `|Q| = 2 ^ n`.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQ
    -- `O_{2'}(Q)` is a `2'`-group, and its order divides `|Q| = 2 ^ n`.
    have hpi : Work.Fitting.IsPiNat (fun q => q ≠ 2)
        (Nat.card ↥(Work.Fitting.pPrimeCore 2 ↥Q)) :=
      Work.Fitting.piCore_isPiNat ↥Q (fun q => q ≠ 2)
    have hcard1 : Nat.card ↥(Work.Fitting.pPrimeCore 2 ↥Q) = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      have hpdvd' : p ∣ 2 ^ n := by
        rw [← hn]
        exact hpdvd.trans (Subgroup.card_subgroup_dvd_card (Work.Fitting.pPrimeCore 2 ↥Q))
      have hp2 : p = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hpdvd') with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact h1
      exact (hpi p hp hpdvd) hp2
    rw [Work.ZassenhausTwoGroup.oddPart]
    exact map_subtype_eq_bot_iff.mpr (Subgroup.card_eq_one.mp hcard1)
  · intro hodd
    -- `Q` is nilpotent, so `Q = O_2(Q) · O_{2'}(Q)`; with `O_{2'}(Q) = ⊥` this gives
    -- `Q = O_2(Q)`.
    have hsplit : Work.ZassenhausTwoGroup.twoPart Q = Q := by
      have h0 := twoPart_sup_oddPart h
      rw [hodd, sup_bot_eq] at h0
      exact h0
    -- Passing to the image under the injective `Q.subtype` does not change the order, so
    -- `|Q| = |O_2(Q)|` is a power of `2`.
    have hcard : Nat.card ↥Q = Nat.card ↥(Work.Fitting.pCore 2 ↥Q) := by
      have h1 : Nat.card ↥Q = Nat.card ↥(Work.ZassenhausTwoGroup.twoPart Q) :=
        (congrArg (fun S : Subgroup G => Nat.card ↥S) hsplit).symm
      have h2 : Nat.card ↥(Work.ZassenhausTwoGroup.twoPart Q) =
          Nat.card ↥(Work.Fitting.pCore 2 ↥Q) := by
        rw [Work.ZassenhausTwoGroup.twoPart]
        exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)
      exact h1.trans h2
    obtain ⟨k, hk⟩ := (Work.Fitting.isPiNat_prime_iff Nat.prime_two).mp
      (Work.Fitting.piCore_isPiNat ↥Q (fun q => q = 2))
    exact (IsPGroup.iff_card (p := 2) (G := ↥Q)).mpr ⟨k, hcard.trans hk⟩

end Work.ZassenhausTwoGroup
