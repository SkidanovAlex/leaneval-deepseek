import Mathlib
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.OrderPrimeCard

namespace Work.L2F.Props.Count

/-- In a finite group `G`, a subgroup `Y` of prime order `r` contains exactly `r - 1` elements of
order `r` (order measured in the ambient group `G`): those are precisely the non-identity
elements of `Y`. -/
theorem card_mem_orderOf_eq_prime {G : Type*} [Group G] [Fintype G] (r : ℕ) (hr : r.Prime)
    (Y : Subgroup G) (hY : Nat.card Y = r) :
    Nat.card {g : G // g ∈ Y ∧ orderOf g = r} = r - 1 := by
  classical
  have e : {g : G // g ∈ Y ∧ orderOf g = r} ≃ {h : Y // orderOf h = r} :=
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, by rw [Subgroup.orderOf_mk, g.2.2]⟩
      invFun := fun h => ⟨h.1.1, h.1.2, by rw [Subgroup.orderOf_coe]; exact h.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [Nat.card_congr e]
  exact OrderPrimeCard hr hY

/-- For a finite group `G` and a prime `r`, half of a classical counting fact: the elements of
order `r` are partitioned by the subgroups of order `r` containing them, each containing exactly
`r - 1` such elements. -/
theorem natCard_orderOf_eq_prime (G : Type*) [Group G] [Fintype G] (r : ℕ) (hr : r.Prime) :
    Nat.card {g : G // orderOf g = r}
      = Nat.card {Y : Subgroup G // Nat.card Y = r} * (r - 1) := by
  classical
  let f : {g : G // orderOf g = r} → {Y : Subgroup G // Nat.card Y = r} :=
    fun a => ⟨Subgroup.zpowers a.1, by rw [Nat.card_zpowers, a.2]⟩
  have hfiber : ∀ Y : {Y : Subgroup G // Nat.card Y = r},
      Nat.card {a : {g : G // orderOf g = r} // f a = Y} = r - 1 := by
    intro Y
    have e : {a : {g : G // orderOf g = r} // f a = Y} ≃
        {g : G // g ∈ (Y : Subgroup G) ∧ orderOf g = r} :=
      { toFun := fun a =>
          ⟨a.1.1, (congrArg Subtype.val a.2 :
              Subgroup.zpowers a.1.1 = (Y : Subgroup G)) ▸ Subgroup.mem_zpowers a.1.1, a.1.2⟩
        invFun := fun x =>
          ⟨⟨x.1, x.2.2⟩, Subtype.ext (Subgroup.eq_of_le_of_card_ge
            (Subgroup.zpowers_le_of_mem x.2.1)
            (by rw [Nat.card_zpowers, x.2.2, Y.2]))⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    rw [Nat.card_congr e]
    exact card_mem_orderOf_eq_prime r hr (Y : Subgroup G) Y.2
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun Y _ => hfiber Y)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

theorem SubgroupCount (G : Type*) [Group G] [Fintype G] (r : ℕ) (hr : r.Prime) :
    (r - 1) * Nat.card {Y : Subgroup G // Nat.card Y = r} = Nat.card {g : G // orderOf g = r} := by
  rw [natCard_orderOf_eq_prime G r hr]
  exact mul_comm _ _

end Work.L2F.Props.Count
