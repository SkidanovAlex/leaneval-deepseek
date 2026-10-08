import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson

theorem zpowers_mul_eq_sup_of_coprime {G : Type} [Group G] {a b : G}
    (hcomm : Commute a b) (hcop : (orderOf a).Coprime (orderOf b)) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b = Subgroup.zpowers (a * b) := by
  obtain ⟨u, v, huv⟩ := hcop.isCoprime
  -- `huv : u * ↑(orderOf a) + v * ↑(orderOf b) = 1`
  have hma : a ∈ Subgroup.zpowers (a * b) := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨v * (orderOf b : ℤ), ?_⟩
    have hb1 : b ^ (v * (orderOf b : ℤ)) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one]
      exact ⟨v, by ring⟩
    have ha1 : a ^ (v * (orderOf b : ℤ)) = a := by
      have h : (orderOf a : ℤ) ∣ (v * (orderOf b : ℤ)) - 1 := by
        use -u
        linarith [huv]
      have h2 := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := a)).mp h
      simpa using h2
    rw [hcomm.mul_zpow, ha1, hb1, mul_one]
  have hmb : b ∈ Subgroup.zpowers (a * b) := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨u * (orderOf a : ℤ), ?_⟩
    have ha1 : a ^ (u * (orderOf a : ℤ)) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one]
      exact ⟨u, by ring⟩
    have hb1 : b ^ (u * (orderOf a : ℤ)) = b := by
      have h : (orderOf b : ℤ) ∣ (u * (orderOf a : ℤ)) - 1 := by
        use -v
        linarith [huv]
      have h2 := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := b)).mp h
      simpa using h2
    rw [hcomm.mul_zpow, ha1, hb1, one_mul]
  exact le_antisymm (sup_le (Subgroup.zpowers_le.mpr hma) (Subgroup.zpowers_le.mpr hmb))
    (Subgroup.zpowers_mul_le_sup a b)

end Work.AppXIDickson
