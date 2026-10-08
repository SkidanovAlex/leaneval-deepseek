import Mathlib
import Submission.Work.BSW.Defs

namespace Work.BSW.Api

/-- A subgroup of prime order is disjoint from its conjugates: if `|P|` is prime and `g ∉ N_G(P)`,
then `P ⊓ P^g = ⊥`.

Indeed `P ⊓ P^g` is a subgroup of `P`, so its order divides `|P|`; if it were not trivial it would
have order `|P|`, forcing `P ≤ P^g` and hence `P = P^g`, i.e. `g ∈ N_G(P)`.

This is the "3.7" input of the Zassenhaus conversion in the cases where the Sylow `p`-subgroup `Q`
has prime order (`q = 5` for `|K| = 2`, `q = 7` for `|K| = 4` with `|G| = 168`). -/
theorem prime_card_inf_conjSub_eq_bot {G : Type} [Group G] [Finite G] {P : Subgroup G} {g : G}
    (hg : g ∉ Subgroup.normalizer (P : Set G)) (hp : Nat.Prime (Nat.card ↥P)) :
    P ⊓ Work.GW2.conjSub g P = ⊥ := by
  have hconj : Work.GW2.conjSub g P ≠ P := fun h =>
    hg ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr h)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hdvd : Nat.card ↥(P ⊓ Work.GW2.conjSub g P) ∣ Nat.card ↥P :=
    Subgroup.card_dvd_of_le inf_le_left
  rcases hp.eq_one_or_self_of_dvd (Nat.card ↥(P ⊓ Work.GW2.conjSub g P)) hdvd with h1 | h2
  · exfalso
    have hbot : P ⊓ Work.GW2.conjSub g P = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  · have hEq : P ⊓ Work.GW2.conjSub g P = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2])
    have hle : P ≤ Work.GW2.conjSub g P := by
      calc P = P ⊓ Work.GW2.conjSub g P := hEq.symm
        _ ≤ Work.GW2.conjSub g P := inf_le_right
    have hcard : Nat.card ↥(Work.GW2.conjSub g P) = Nat.card ↥P := by
      rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hconj (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

end Work.BSW.Api
