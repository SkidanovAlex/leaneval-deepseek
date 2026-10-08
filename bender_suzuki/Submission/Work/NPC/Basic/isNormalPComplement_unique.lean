import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Basic

/-- Auxiliary: if `N` and `M` are normal `p`-complements then `N ≤ M`.
The proof sends `n ∈ N` to the quotient `G ⧸ M`, a `p`-group; the order of the image
divides `p ^ k` for some `k` and also divides `|N|` (coprime to `p`), hence is `1`,
so `n ∈ M`. -/
private theorem le_of_isNormalPComplement {G : Type*} [Group G] [Finite G] {p : ℕ}
    {N M : Subgroup G} (hN : Work.NPC.IsNormalPComplement p N)
    (hM : Work.NPC.IsNormalPComplement p M) : N ≤ M := by
  have hMn : M.Normal := hM.normal
  intro n hn
  set d : ℕ := orderOf ((QuotientGroup.mk' M) n) with hd
  have h1 : d ∣ Nat.card N := by
    rw [hd]
    refine (orderOf_map_dvd (QuotientGroup.mk' M) n).trans ?_
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hn)
  have hcop : d.Coprime p := hN.coprime_card.coprime_dvd_left h1
  obtain ⟨k, hk⟩ := hM.isPGroup_quotient.exists_orderOf_dvd_pow ((QuotientGroup.mk' M) n)
  have hk' : d ∣ p ^ k := by rw [hd]; exact hk
  have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_right k) dvd_rfl hk'
  have hq : ((QuotientGroup.mk' M) n) = 1 := by
    rw [← orderOf_eq_one_iff, ← hd]
    exact hd1
  exact (QuotientGroup.eq_one_iff n).mp hq

theorem isNormalPComplement_unique {G : Type*} [Group G] [Finite G] {p : ℕ}
    {N M : Subgroup G} (hN : Work.NPC.IsNormalPComplement p N)
    (hM : Work.NPC.IsNormalPComplement p M) : N = M := by
  exact le_antisymm (le_of_isNormalPComplement hN hM) (le_of_isNormalPComplement hM hN)

end Work.NPC.Basic
