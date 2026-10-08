import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.dihOrCycSylow_subgroup

/-!
# CORE2A: elementary structure of `O₂(Ĥ)` in Bender's setting

This file collects the elementary (and independently useful) facts about `V = O₂(Ĥ) =
pCoreIn 2 B.Hhat` that the proof of Bender's Theorem 2.6 (first paragraph) needs:

* `V ≤ Ĥ`, `V` is a `2`-group, `V` is normalised by `Ĥ`, `V ≤ S`;
* `t` is the unique involution of `S₀`, and if `V ≤ S₀` then `Ĥ = C(t) = H`;
* if `V ⊄ S₀` then `V ∩ S₀ = ⟨t⟩` and `[S : V] ≤ 2`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

variable {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)

/-- `O₂(Ĥ)` is a subgroup of `Ĥ`. -/
theorem pCoreIn_le_Hhat : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _

/-- `O₂(Ĥ)` is a `2`-group. -/
theorem pCoreIn_isPGroup : IsPGroup 2 (Work.GW2.pCoreIn 2 B.Hhat) := by
  have h : IsPGroup 2 (Work.GW2.pCore 2 ↥B.Hhat) := by
    have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}) :=
      Sylow.sSup_of_normal {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}
        (fun N hN => hN.2) (fun N hN => hN.1)
    exact hsup.to_le (Subgroup.normalCore_le _)
  exact h.map B.Hhat.subtype

/-- `O₂(Ĥ)` is normalised by `Ĥ`. -/
theorem conj_mem_pCoreIn {h x : G} (hh : h ∈ B.Hhat)
    (hx : x ∈ Work.GW2.pCoreIn 2 B.Hhat) : h * x * h⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  haveI : (Work.GW2.pCore 2 ↥B.Hhat).Normal :=
    Subgroup.normalCore_normal (sSup {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N})
  obtain ⟨y, hy, hyx⟩ := hx
  have hmem : (⟨h, hh⟩ : ↥B.Hhat) * y * (⟨h, hh⟩ : ↥B.Hhat)⁻¹ ∈ Work.GW2.pCore 2 ↥B.Hhat :=
    Subgroup.Normal.conj_mem ‹(Work.GW2.pCore 2 ↥B.Hhat).Normal› y hy _
  refine ⟨(⟨h, hh⟩ : ↥B.Hhat) * y * (⟨h, hh⟩ : ↥B.Hhat)⁻¹, hmem, ?_⟩
  rw [← hyx]
  simp

/-- A Sylow `2`-subgroup of `Ĥ` with underlying subgroup `S`: since `S` is a Sylow
`2`-subgroup of `G`, no strictly larger `2`-subgroup of `Ĥ` exists. -/
theorem sylow_subgroupOf_Hhat :
    ∃ Q : Sylow 2 ↥B.Hhat, (Q : Subgroup ↥B.Hhat) = (B.S : Subgroup G).subgroupOf B.Hhat := by
  have hle := bSetup_S_le_Hhat B
  have hpg : IsPGroup 2 ↥((B.S : Subgroup G).subgroupOf B.Hhat) :=
    ((B.S).isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  refine ⟨⟨((B.S : Subgroup G).subgroupOf B.Hhat), hpg, ?_⟩, rfl⟩
  intro Q hQ hle'
  have hmapQ : IsPGroup 2 ↥(Q.map B.Hhat.subtype) := hQ.map B.Hhat.subtype
  have hleS : (B.S : Subgroup G) ≤ Q.map B.Hhat.subtype := by
    intro x hx
    have hx' : (⟨x, hle hx⟩ : ↥B.Hhat) ∈ (B.S : Subgroup G).subgroupOf B.Hhat := hx
    exact Subgroup.mem_map_of_mem B.Hhat.subtype (hle' hx')
  have hSmax : Q.map B.Hhat.subtype = (B.S : Subgroup G) :=
    (B.S).is_maximal' hmapQ hleS
  refine le_antisymm ?_ hle'
  intro y hy
  have : ((y : ↥B.Hhat) : G) ∈ (B.S : Subgroup G) := by
    rw [← hSmax]
    exact Subgroup.mem_map_of_mem B.Hhat.subtype hy
  exact this

/-- `O₂(Ĥ) ≤ S`: a normal `2`-subgroup lies in every Sylow `2`-subgroup. -/
theorem pCoreIn_le_S : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := sylow_subgroupOf_Hhat B
  have h1 : Work.GW2.pCore 2 ↥B.Hhat ≤ (Q : Subgroup ↥B.Hhat) := by
    refine IsPGroup.le_sylow_of_normal ?_ Q
    have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}) :=
      Sylow.sSup_of_normal {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}
        (fun N hN => hN.2) (fun N hN => hN.1)
    exact hsup.to_le (Subgroup.normalCore_le _)
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyQ : y ∈ (Q : Subgroup ↥B.Hhat) := h1 hy
  rw [← hyx, hQ] at *
  exact hyQ

/-- The cyclic group `S₀` has a unique involution, namely `t`. -/
theorem eq_t_of_mem_S0_orderOf_eq_two {x : G} (hx : x ∈ B.S0) (hx2 : orderOf x = 2) :
    x = B.t := by
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  have h := eq_of_orderOf_eq_two_of_isCyclic (a := (⟨x, hx⟩ : ↥B.S0))
    (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
    (by rw [Subgroup.orderOf_mk]; exact hx2) (by rw [Subgroup.orderOf_mk]; exact B.t_order)
  exact congrArg Subtype.val h

/-- If `O₂(Ĥ) ≤ S₀` (and `O₂(Ĥ) ≠ 1`) then `t ∈ O₂(Ĥ)`, so `⟨t⟩` is normal in `Ĥ` and hence
`Ĥ = C(t) = H`: this is the first case of the dichotomy. -/
theorem Hhat_eq_H_of_pCoreIn_le_S0 (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥)
    (hle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) : B.Hhat = B.H := by
  have hpg : IsPGroup 2 (Work.GW2.pCoreIn 2 B.Hhat) := pCoreIn_isPGroup B
  -- `V` is nontrivial of `2`-power order, so `2 ∣ |V|` and Cauchy gives an involution.
  have h2dvd : 2 ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
    rcases hpg.card_eq_or_dvd (p := 2) with h1 | h2
    · exfalso
      exact hV (Subgroup.card_eq_one.mp h1)
    · exact h2
  obtain ⟨x, hx2⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.pCoreIn 2 B.Hhat)) 2 h2dvd
  -- `x` lies in the cyclic group `S₀` and is an involution, hence `x = t`.
  have hxmem : ((x : ↥(Work.GW2.pCoreIn 2 B.Hhat)) : G) ∈ B.S0 := hle x.2
  have hxe : ((x : ↥(Work.GW2.pCoreIn 2 B.Hhat)) : G) = B.t :=
    eq_t_of_mem_S0_orderOf_eq_two B hxmem (by rw [Subgroup.orderOf_coe]; exact hx2)
  have htV : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := hxe ▸ x.2
  -- `t` is the only involution of the normal `2`-subgroup `V`, so it is central in `Ĥ`.
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  haveI : IsCyclic ↥(Work.GW2.pCoreIn 2 B.Hhat) := isCyclic_of_le hle
  have hcen : ∀ h ∈ B.Hhat, h * B.t * h⁻¹ = B.t := by
    intro h hh
    have hmem : h * B.t * h⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat := conj_mem_pCoreIn B hh htV
    have hsemi : SemiconjBy h B.t (h * B.t * h⁻¹) := by simp [SemiconjBy, mul_assoc]
    have hord : orderOf (h * B.t * h⁻¹) = 2 :=
      (SemiconjBy.orderOf_eq h hsemi).symm.trans B.t_order
    have h2 : (⟨h * B.t * h⁻¹, hmem⟩ : ↥(Work.GW2.pCoreIn 2 B.Hhat)) = ⟨B.t, htV⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    exact congrArg Subtype.val h2
  refine le_antisymm ?_ B.H_le_Hhat
  intro h hh
  rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  calc B.t * h = (h * B.t * h⁻¹) * h := by rw [hcen h hh]
    _ = h * B.t := by simp [mul_assoc]

end Work.CORE2A
