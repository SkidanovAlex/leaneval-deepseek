import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.kEqSmall

namespace Work.BG

set_option linter.style.haveILetI false

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG 1981, small case `|S| = 4`.**  When the Sylow 2-subgroup is the Klein four group
(`D.n = 2`) the subgroup `B₁ = U ∩ C(t₁)` meets the maximal odd subgroup `K₂` inverted by
`t₂` trivially.

For `n = 2` the group `S` has order `4` and `S₀` has order `2`, so `t` and `t₁t₂` are the
unique involution of the cyclic group `S₀`; hence `t = t₁t₂`.  If `x ∈ B₁ ∩ K₂`, then `t`
centralizes `x` (as `x ∈ U ≤ H = C(t)`), `t₁` centralizes `x` (as `x ∈ B₁`), and `t₂`
inverts `x` (as `x ∈ K₂`).  Therefore
`x = t x t⁻¹ = (t₁t₂) x (t₁t₂)⁻¹ = t₁ (t₂ x t₂⁻¹) t₁⁻¹ = t₁ x⁻¹ t₁⁻¹ = x⁻¹`,
so `x² = 1`.  Since `K₂` has odd order, `x = 1`. -/
theorem b1InfK2EqBot {G : Type} [Group G] [Finite G] (D : BGData G) (K2 : Subgroup G)
    (hn : D.n = 2) (hK2 : IsMaxInverted D.H D.t2 K2) : D.B1 ⊓ K2 = ⊥ := by
  -- `U ≤ H`.
  have hU : D.U ≤ D.H := by
    show (Work.GW2.oddCore ↥D.H).map D.H.subtype ≤ D.H
    exact Subgroup.map_subtype_le _
  -- `S` has order `4` when `n = 2`.
  have hS : Nat.card (D.S : Subgroup G) = 4 := by
    obtain ⟨e⟩ := D.dih
    rw [hn] at e
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- `S₀` has order `2`, hence `t = t₁t₂`.
  have hS0 : Nat.card ↥D.S0 = 2 := by
    have h := Subgroup.relIndex_mul_card D.S0 (D.S : Subgroup G)
    rw [D.S0_index, inf_eq_left.mpr D.S0_le, hS] at h
    omega
  have hmem : D.t1 * D.t2 ∈ D.S0 := by rw [D.gen]; exact Subgroup.mem_zpowers _
  have hord12 : orderOf (D.t1 * D.t2) = 2 := by
    have h := Nat.card_zpowers (D.t1 * D.t2)
    rw [← D.gen] at h
    omega
  have ht : D.t = D.t1 * D.t2 := by
    haveI : IsCyclic ↥D.S0 := D.S0_cyclic
    have key := eq_of_orderOf_eq_two_of_isCyclic (C := ↥D.S0)
      (a := (⟨D.t, D.t_mem⟩ : ↥D.S0)) (b := (⟨D.t1 * D.t2, hmem⟩ : ↥D.S0))
      (by rw [Subgroup.orderOf_mk]; exact D.t_order)
      (by rw [Subgroup.orderOf_mk]; exact hord12)
    exact congrArg Subtype.val key
  -- main argument
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxB1, hxK2⟩ := hx
  have hxB1' : x ∈ D.U ⊓ Subgroup.centralizer ({D.t1} : Set G) := hxB1
  rw [Subgroup.mem_inf] at hxB1'
  obtain ⟨hxU, hxC1⟩ := hxB1'
  have hxH : x ∈ D.H := hU hxU
  have hxt : D.t * x * D.t⁻¹ = x := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hxH
    exact mul_inv_eq_iff_eq_mul.mpr h.symm
  have hxt1 : D.t1 * x * D.t1⁻¹ = x := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hxC1
    exact mul_inv_eq_iff_eq_mul.mpr h.symm
  have hxt2 : D.t2 * x * D.t2⁻¹ = x⁻¹ := hK2.2.2.1 x hxK2
  have htx : D.t * x * D.t⁻¹ = x⁻¹ := by
    rw [ht]
    calc (D.t1 * D.t2) * x * (D.t1 * D.t2)⁻¹
        = D.t1 * (D.t2 * x * D.t2⁻¹) * D.t1⁻¹ := by group
      _ = D.t1 * x⁻¹ * D.t1⁻¹ := by rw [hxt2]
      _ = (D.t1 * x * D.t1⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hxt1]
  have hxinv : x = x⁻¹ := hxt.symm.trans htx
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hxinv
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
  have hdvdK : orderOf x ∣ Nat.card ↥K2 := by
    rw [← Subgroup.orderOf_mk x hxK2]
    exact orderOf_dvd_natCard _
  have hnot : ¬ (2 ∣ Nat.card ↥K2) := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hK2.2.1) (even_iff_two_dvd.mpr h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hdvdK) hnot

end Work.BG
