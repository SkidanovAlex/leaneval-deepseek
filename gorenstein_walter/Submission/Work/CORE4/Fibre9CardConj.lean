import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

/-- Two distinct subgroups of prime order intersect trivially: the cardinality of the
intersection divides the prime `p`, and equality of cardinalities together with one inclusion
forces equality of the subgroups. -/
theorem Fibre9CardConj {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {P Y : Subgroup G}
    (hPcard : Nat.card P = p) (hYc : ∃ g : G, Y = Work.GW2.conjSub g P) (hYne : Y ≠ P) :
    Nat.card ↥Y = p ∧ Y ⊓ P = ⊥ := by
  obtain ⟨g, rfl⟩ := hYc
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (hPcard.symm ▸ hp.ne_zero)
  -- the conjugate of `P` has the same cardinality as `P`
  have hYcard : Nat.card ↥(Work.GW2.conjSub g P) = p := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard]
  refine ⟨hYcard, ?_⟩
  -- the intersection lies in `P`, so its cardinality divides the prime `p`
  have hdvd : Nat.card ↥(Work.GW2.conjSub g P ⊓ P) ∣ p := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · -- equality of orders would force `P ≤ P^g`, hence `P^g = P`
    exfalso
    haveI : Finite ↥(Work.GW2.conjSub g P) :=
      Nat.finite_of_card_ne_zero (hYcard.symm ▸ hp.ne_zero)
    have hPeq : Work.GW2.conjSub g P ⊓ P = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hPcard, hp']))
    have hle : P ≤ Work.GW2.conjSub g P := hPeq.symm.le.trans inf_le_left
    have heq : Work.GW2.conjSub g P = P :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hYcard, hPcard]))).symm
    exact hYne heq

end Work.CORE4
