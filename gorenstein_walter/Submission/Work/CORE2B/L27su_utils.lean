import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.Dihedral.Defs

/-!
# CORE2B — elementary consequences of the `BenderSetup` fields (shared utilities)

This module carries the handful of elementary facts about Bender's fixed notation
(`S`, `t`, `H = C_G(t)`, `U = O(H)`) that *many* modules of the area need:

* `L27su_S_le_H` — `S ≤ H = C_G(t)` (`t` is central in the dihedral Sylow `S`);
* `L27su_H_le_normalizer_U`, `L27su_S_le_normalizer_U` — `H ≤ N_G(U)`, `S ≤ N_G(U)`;
* `L27su_S_dihedral` — `S ≃* DihedralGroup n` with `n ≥ 2`, so that the toolbox field `split`
  (`H = U ⊔ S`) applies;
* `L27su_le_of_sup_isPGroup`, `L27su_odd_subgroup_le_U` — every odd-order subgroup of `H` lies in
  `U = O(H)`.

They originally lived in `Submission.Work.CORE2B.L27_su_not_le_h22_proved`.  They are split off
here because that target file is a *consumer* of the transport module
`Submission.Work.CORE2B.L27su_transport` (and of `…L27su_two_core_le_pCoreIn_Hhat`), which in turn
import it — so the shared lemmas have to be importable without dragging in the target.  The
target file imports this module, so every consumer of the target still sees them.
-/

namespace Work.CORE2B

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `S ≤ H = C_G(t)`: `t` is central in the dihedral Sylow `S` (`t_central_in_S`). -/
theorem L27su_S_le_H (B : Work.GW2.BenderSetup G) : (B.S : Subgroup G) ≤ B.H := by
  intro x hx
  rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (t_central_in_S B x hx).symm

/-- `H ≤ N_G(U)`: `U = O(H) ◁ H`. -/
theorem L27su_H_le_normalizer_U (B : Work.GW2.BenderSetup G) :
    B.H ≤ Subgroup.normalizer (B.U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh u hu
  have hu' : u ∈ (Work.GW2.oddCore ↥B.H).map B.H.subtype := hu
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu'
  exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥B.H) * y * (⟨h, hh⟩ : ↥B.H)⁻¹,
    (Work.GW2.oddCore_normal ↥B.H).conj_mem y hy _, rfl⟩

/-- Every element of `S` normalizes `U`. -/
theorem L27su_S_le_normalizer_U (B : Work.GW2.BenderSetup G) :
    (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
  (L27su_S_le_H B).trans (L27su_H_le_normalizer_U B)

/-- `S ≅ DihedralGroup n` with `n ≥ 2` (so that the toolbox `split` applies). -/
theorem L27su_S_dihedral (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  rcases hCtx.sylow B.S with h | h
  · exact absurd h hnc
  · obtain ⟨n, h⟩ := h
    obtain ⟨e⟩ := h
    obtain ⟨heven, hne⟩ :=
      Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e B.S.isPGroup' hnc
    haveI := hne
    obtain ⟨k, hk⟩ := heven
    have hn2 : 2 ≤ n := by
      have h0 : n ≠ 0 := NeZero.ne n
      omega
    exact ⟨n, hn2, ⟨e⟩⟩

/-- If `U ◁ G`, `U ⊔ S = ⊤` with `S` a `2`-group, then every subgroup of odd order lies in `U`. -/
theorem L27su_le_of_sup_isPGroup {U S X : Subgroup G}
    [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S) (hX : Odd (Nat.card X)) : X ≤ U := by
  have h1 : U.relIndex X ∣ U.index := Subgroup.relIndex_dvd_index_of_normal U X
  have hidx : U.index = U.relIndex S := by
    rw [← Subgroup.relIndex_top_right, ← hUS, Subgroup.relIndex_sup_left]
  have h2 : U.relIndex X ∣ U.relIndex S := hidx ▸ h1
  have h3 : U.relIndex X ∣ Nat.card S := h2.trans (Subgroup.relIndex_dvd_card U S)
  have h4 : U.relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card U X
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS
  have h5 : U.relIndex X ∣ 2 ^ n := hn ▸ h3
  have hnot : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hX
  have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := n) hnot).symm
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h5 h4)

/-- Odd-order subgroups of `H = C_G(t)` are contained in `U = O(H)` (using `H = U ⊔ S`). -/
theorem L27su_odd_subgroup_le_U (T : Work.GW2.LocalToolkit) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∀ X : Subgroup G, X ≤ B.H → Odd (Nat.card X) → X ≤ B.U := by
  obtain ⟨n, hn, ⟨e⟩⟩ := L27su_S_dihedral hCtx B
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G B.S n hn ⟨e⟩ B.t (B.S0_le B.t_mem) B.t_order (t_central_in_S B)
  intro X hXH hXodd
  have hUeq : B.U = Work.GW2.oddCoreIn B.H := rfl
  have hle : B.U ≤ B.H := Subgroup.map_subtype_le _
  have hSle : (B.S : Subgroup G) ≤ B.H := L27su_S_le_H B
  have hU'eq : B.U.subgroupOf B.H = Work.GW2.oddCore ↥B.H := by
    rw [hUeq, Work.GW2.oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective B.H.subtype_injective _
  have hUnorm : (B.U.subgroupOf B.H).Normal := hU'eq ▸ Work.GW2.oddCore_normal ↥B.H
  have hUS' : B.U.subgroupOf B.H ⊔ (B.S : Subgroup G).subgroupOf B.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle hSle, hsplit, Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 ((B.S : Subgroup G).subgroupOf B.H) := B.S.isPGroup'.comap_subtype
  have hXcard : Nat.card (X.subgroupOf B.H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hXodd' : Odd (Nat.card (X.subgroupOf B.H)) := hXcard.symm ▸ hXodd
  have hX' : X.subgroupOf B.H ≤ B.U.subgroupOf B.H := by
    haveI : (B.U.subgroupOf B.H).Normal := hUnorm
    exact L27su_le_of_sup_isPGroup hUS' hS' hXodd'
  intro x hx
  have hxH : x ∈ B.H := hXH hx
  have hmem1 : (⟨x, hxH⟩ : ↥B.H) ∈ X.subgroupOf B.H := Subgroup.mem_subgroupOf.mpr hx
  have hmem2 : (⟨x, hxH⟩ : ↥B.H) ∈ B.U.subgroupOf B.H := hX' hmem1
  simpa using Subgroup.mem_subgroupOf.mp hmem2

end Work.CORE2B
