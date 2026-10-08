import Mathlib
import Submission.Work.BG.S_le_H
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

set_option linter.style.haveILetI false

-- Do NOT import `Submission.Work.BG.kEqSmall`: that module and `Submission.Work.BG.S_le_H` both
-- declare `Work.BG.eq_of_orderOf_eq_two_of_isCyclic`, so the two cannot be imported into one
-- file.  Reproduce the (already known) proof of `Work.BG.kEqSmall` here, using the copy of
-- `Work.BG.eq_of_orderOf_eq_two_of_isCyclic` that comes from `Submission.Work.BG.S_le_H`.
open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **G5** (BG 1981, `|S| = 4`): `C_H(t₁) = C_H(t₂)`, so `k₁ = k₂`.

For `n = 2` the Sylow 2-subgroup `S` has order `4`, hence `S₀` has order `2`; the two elements
`t` and `t₁t₂` of the (cyclic) group `S₀` both have order `2`, so `t = t₁t₂`.  Then
`t₂ = t₁t`, `t₁ = t₂t`, and consequently any `x` commuting with `t` and one `tᵢ` commutes with
the other: `C(t₁) ⊓ C(t) = C(t₂) ⊓ C(t)`, whence the relative indices agree. -/
theorem kEqSmallAlt : Work.GW2.C16.KEqSmallProp := by
  intro G _ _ D hn
  -- `S` has order `4`.
  have hS : Nat.card (D.S : Subgroup G) = 4 := by
    obtain ⟨e⟩ := D.dih
    rw [hn] at e
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- hence `S₀` (of relative index two in `S`) has order `2`.
  have hS0 : Nat.card ↥D.S0 = 2 := by
    have h := Subgroup.relIndex_mul_card D.S0 (D.S : Subgroup G)
    rw [D.S0_index, inf_eq_left.mpr D.S0_le, hS] at h
    omega
  -- `t₁t₂` generates `S₀`, so it also has order `2`.
  have hmem : D.t1 * D.t2 ∈ D.S0 := by rw [D.gen]; exact Subgroup.mem_zpowers _
  have hord12 : orderOf (D.t1 * D.t2) = 2 := by
    have h := Nat.card_zpowers (D.t1 * D.t2)
    rw [← D.gen] at h
    omega
  -- both `t` and `t₁t₂` are the unique involution of the cyclic group `S₀`.
  have ht : D.t = D.t1 * D.t2 := by
    haveI : IsCyclic ↥D.S0 := D.S0_cyclic
    have key := eq_of_orderOf_eq_two_of_isCyclic (C := ↥D.S0)
      (a := (⟨D.t, D.t_mem⟩ : ↥D.S0)) (b := (⟨D.t1 * D.t2, hmem⟩ : ↥D.S0))
      (by rw [Subgroup.orderOf_mk]; exact D.t_order)
      (by rw [Subgroup.orderOf_mk]; exact hord12)
    exact congrArg Subtype.val key
  -- `t₁² = t₂² = 1`, hence `t₂ = t₁t` and `t₁ = t₂t`.
  have h1sq : D.t1 * D.t1 = 1 := by
    rw [← pow_two, ← D.t1_order]
    exact pow_orderOf_eq_one D.t1
  have h2sq : D.t2 * D.t2 = 1 := by
    rw [← pow_two, ← D.t2_order]
    exact pow_orderOf_eq_one D.t2
  have ht2 : D.t2 = D.t1 * D.t := by
    rw [ht, ← mul_assoc, h1sq, one_mul]
  have ht1 : D.t1 = D.t * D.t2 := by
    rw [ht, mul_assoc, h2sq, mul_one]
  -- `C(t₁) ⊓ C(t) = C(t₂) ⊓ C(t)`.
  have hC : (Subgroup.centralizer ({D.t1} : Set G)) ⊓ D.H = (Subgroup.centralizer ({D.t2} : Set G)) ⊓ D.H := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      Work.GW2.BGData.H]
    constructor
    · rintro ⟨h1, h0⟩
      exact ⟨by rw [ht2]; exact Commute.mul_left h1 h0, h0⟩
    · rintro ⟨h2, h0⟩
      exact ⟨by rw [ht1]; exact Commute.mul_left h0 h2, h0⟩
  -- pass to subgroups of `H` and take indices.
  have hsub : (Subgroup.centralizer ({D.t1} : Set G)).subgroupOf D.H
      = (Subgroup.centralizer ({D.t2} : Set G)).subgroupOf D.H := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : (x : G) ∈ Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H := ⟨hx, x.2⟩
      rw [hC] at h1
      exact h1.1
    · intro hx
      have h1 : (x : G) ∈ Subgroup.centralizer ({D.t2} : Set G) ⊓ D.H := ⟨hx, x.2⟩
      rw [← hC] at h1
      exact h1.1
  exact congrArg Subgroup.index hsub

end Work.BG
