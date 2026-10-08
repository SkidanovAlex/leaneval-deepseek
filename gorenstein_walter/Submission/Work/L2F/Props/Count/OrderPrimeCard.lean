import Mathlib

namespace Work.L2F.Props.Count

theorem OrderPrimeCard {H : Type*} [Group H] [Fintype H] {r : ℕ} (hr : r.Prime)
    (hH : Nat.card H = r) : Nat.card {h : H // orderOf h = r} = r - 1 := by
  classical
  have hr1 : r ≠ 1 := hr.ne_one
  have hcardH : Fintype.card H = r := by
    rw [← Nat.card_eq_fintype_card]; exact hH
  -- The elements of order `r` are exactly the non-identity elements.
  have hequiv : {h : H // orderOf h = r} ≃ {h : H // h ≠ 1} :=
  { toFun := fun h => ⟨h.1, fun h1 => by
      have ho : orderOf h.1 = 1 := by rw [h1, orderOf_one]
      have : r = 1 := by rw [← h.2, ho]
      exact hr1 this⟩
    invFun := fun h => ⟨h.1, by
      have hdvd : orderOf h.1 ∣ r := by
        rw [← hcardH]; exact orderOf_dvd_card
      rcases hr.eq_one_or_self_of_dvd (orderOf h.1) hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) h.2
      · exact h1⟩
    left_inv := fun h => by ext; rfl
    right_inv := fun h => by ext; rfl }
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card]
  have hcompl : Fintype.card {h : H // h ≠ 1}
      = Fintype.card H - Fintype.card {h : H // h = 1} :=
    Fintype.card_subtype_compl (fun h : H => h = 1)
  rw [hcompl, Fintype.card_subtype_eq 1, hcardH]

end Work.L2F.Props.Count
