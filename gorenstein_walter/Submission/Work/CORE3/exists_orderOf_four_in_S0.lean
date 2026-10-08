import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.exists_orderOf_four_sq_eq
import Submission.Work.CORE2A.bswHyps2_of_config2

/-!
# `t` is the square of an element of order `4` of `S₀`

Bender 1981, §3 (p. 222): with `S ∈ Syl₂(G)` dihedral and `S₀ ≤ S` the cyclic subgroup of
index two, the involution `t ∈ S₀` is the square of an element of `S₀` of order four, i.e.
`S₀ = ⟨s⟩` with `s² = t`.  Equivalently `4 ∣ |S₀|`, i.e. `|S| ≥ 8`.

The point of the proof is that the ambient `BenderSetup` data alone do **not** rule out
`|S| = 4` (`S` Klein four, `S₀ = ⟨t⟩` of order two; this happens e.g. for `S ∈ Syl₂(A₅)`):
the §3 configuration carried by `D : Case1aData B` does.

Let `P = O_p(U) ≠ 1` (`Work.CORE3.Case1aP_ne_bot`), where `t₁` centralizes `P` and `t₂`
inverts `P` (`D.cent`, `D.inv`).  Since `S₀` has index two in `S` and `t₁, t₂ ∈ S − S₀`, the
product `u = t₁t₂` lies in `S₀` (`Subgroup.relIndex_eq_two_iff_exists_notMem_and'`).  If
`|S₀| = 2` then `S₀ = {1, t}` and hence `u = 1` or `u = t`; in both cases `u` *commutes* with
`P` (`P ≤ U = O(H) ≤ H = C_G(t)`, and `1` is central) and *inverts* `P` (conjugation by
`u = t₁t₂` is inversion), so `P` has exponent `2`; as `|U|` (and hence `|P|`) is odd,
`P = 1` — contradicting `P ≠ 1` (`Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd`).

Hence `|S₀| ≠ 2`.  Together with `2 ∣ |S₀|` (Lagrange, `orderOf t = 2`) this gives
`4 ≤ |S₀|`, and `Work.CORE3.exists_orderOf_four_sq_eq` produces the required `s`.
-/

set_option linter.unusedVariables false

namespace Work.CORE3

open Subgroup

theorem exists_orderOf_four_in_S0 {G : Type} [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) :
    ∃ s ∈ B.S0, orderOf s = 4 ∧ s * s = B.t := by
  classical
  -- `P = O_p(U) ≠ 1`, `P ≤ U ≤ H = C_G(t)`, and `|U|` is odd
  have hPne : Work.GW2.pCoreIn D.p B.U ≠ ⊥ := Case1aP_ne_bot G B D
  have hPU : Work.GW2.pCoreIn D.p B.U ≤ B.U := Subgroup.map_subtype_le _
  have hPUH : Work.GW2.pCoreIn D.p B.U ≤ B.H := hPU.trans (Work.CORE2A.bSetup_U_le_H B)
  have hoddP : Odd (Nat.card ↥(Work.GW2.pCoreIn D.p B.U)) :=
    Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (Subgroup.card_dvd_of_le hPU)
  -- `u = t₁t₂ ∈ S₀` because `S₀` has index two in `S` and `t₁, t₂ ∉ S₀`
  have huS0 : D.t1 * D.t2 ∈ B.S0 := by
    obtain ⟨a, _haS, _haS0, ha⟩ :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := B.S0)
        (K := (B.S : Subgroup G))).mp B.S0_index
    have h1 : a * D.t1 ∈ B.S0 := (ha D.t1 D.t1_mem).resolve_right D.t1_nmem
    have h2 : a * D.t2 ∈ B.S0 := (ha D.t2 D.t2_mem).resolve_right D.t2_nmem
    have h3 : (a * D.t1)⁻¹ * (a * D.t2) ∈ B.S0 := B.S0.mul_mem (B.S0.inv_mem h1) h2
    have hsq : D.t1 * D.t1 = 1 := by
      rw [← pow_two, ← D.t1_order]
      exact pow_orderOf_eq_one D.t1
    have h4 : (a * D.t1)⁻¹ * (a * D.t2) = D.t1 * D.t2 := by
      rw [mul_inv_rev, inv_eq_iff_mul_eq_one.mpr hsq]
      group
    rwa [h4] at h3
  -- conjugation by `u = t₁t₂` inverts `P`
  have hu_inv : Work.GW2.Inverts (D.t1 * D.t2) (Work.GW2.pCoreIn D.p B.U) := by
    intro x hx
    have h2 : D.t2 * x * D.t2⁻¹ = x⁻¹ := D.inv x hx
    have hxinv : x⁻¹ ∈ Work.GW2.pCoreIn D.p B.U := Subgroup.inv_mem _ hx
    have h1 : D.t1 * x⁻¹ = x⁻¹ * D.t1 :=
      Subgroup.mem_centralizer_iff.mp (D.cent hxinv) D.t1 (by simp)
    calc (D.t1 * D.t2) * x * (D.t1 * D.t2)⁻¹
        = D.t1 * (D.t2 * x * D.t2⁻¹) * D.t1⁻¹ := by group
      _ = D.t1 * x⁻¹ * D.t1⁻¹ := by rw [h2]
      _ = x⁻¹ * D.t1 * D.t1⁻¹ := by rw [h1]
      _ = x⁻¹ := by group
  have hncard : (B.S0 : Set G).ncard = Nat.card ↥B.S0 :=
    (Nat.card_coe_set_eq (B.S0 : Set G)).symm
  -- `|S₀| = 2` is impossible: then `u ∈ S₀ = {1, t}` commutes with and inverts `P`
  have hcard2 : Nat.card ↥B.S0 ≠ 2 := by
    intro hc2
    have hsub : ({1, B.t} : Set G) ⊆ (B.S0 : Set G) := by
      intro x hx
      rcases (by simpa using hx : x = 1 ∨ x = B.t) with rfl | rfl
      · exact B.S0.one_mem
      · exact B.t_mem
    have hset : ({1, B.t} : Set G) = (B.S0 : Set G) := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      rw [Set.ncard_pair (Work.CORE2A.bSetup_t_ne_one B).symm, hncard, hc2]
    have hu : D.t1 * D.t2 = 1 ∨ D.t1 * D.t2 = B.t := by
      have hmem : D.t1 * D.t2 ∈ ({1, B.t} : Set G) := hset.symm ▸ huS0
      simpa using hmem
    -- `u` commutes with `P`: `1` is central, and `t ∈ Z(S) ⊆ C_G(P)` because `P ≤ U ≤ H`
    have hPleC : Work.GW2.pCoreIn D.p B.U ≤
        Subgroup.centralizer ({D.t1 * D.t2} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rcases hu with h | h
      · rw [h]; simp
      · rw [h]; exact Subgroup.mem_centralizer_iff.mp (hPUH hx) B.t (by simp)
    -- commuting with and inverting `P` forces `P` to have exponent `2`, hence `P = 1`
    have hbot := Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd hu_inv hoddP
    exact hPne (by
      rw [← hbot]
      exact le_antisymm (fun x hx => ⟨hx, hPleC hx⟩) inf_le_left)
  have hdvd2 : 2 ∣ Nat.card ↥B.S0 := by
    have h := Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
    rwa [B.t_order] at h
  have hpos : 0 < Nat.card ↥B.S0 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd2
  have h4 : 4 ≤ Nat.card ↥B.S0 := by omega
  exact Work.CORE3.exists_orderOf_four_sq_eq B.S0_le B.S.isPGroup' B.S0_cyclic B.t_mem
    B.t_order h4

end Work.CORE3
