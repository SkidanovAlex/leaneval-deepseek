import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2Parity
import Submission.Work.PSL2.Card

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

/-- §4 (10) with the *canonical* field order `q = qOf h` of §4 (9) (instead of the arbitrary
witness `Case2Parity` picks): there are `k` (even) and `k'` (odd) with `{2k, 2k'} = {qOf h ± 1}`
and `|M : M ⊓ H| = qOf h · k'`.  This is the form `Case2NumericImpl` needs (`q = qOf h`), and it
follows from `Case2Parity` by re-running its argument with the witness `(nineP h, nineK h)` of
`h.nine` (`nineP_iso`, `nineP_odd`, `nineP_seven`). -/
theorem Case2ParityQOf :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ k k' : ℕ, Odd (Work.CORE4.qOf h) ∧ 7 ≤ Work.CORE4.qOf h ∧ Even k ∧ Odd k' ∧
          ((2 * k = Work.CORE4.qOf h + 1 ∧ 2 * k' = Work.CORE4.qOf h - 1) ∨
            (2 * k = Work.CORE4.qOf h - 1 ∧ 2 * k' = Work.CORE4.qOf h + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = Work.CORE4.qOf h * k' := by
  intro G _ _ I hbc B h
  classical
  -- work with the canonical witness `(p, m) = (nineP h, nineK h)` of `h.nine`
  change ∃ k k' : ℕ, Odd (Work.CORE4.nineP h ^ Work.CORE4.nineK h) ∧
      7 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h ∧ Even k ∧ Odd k' ∧
      ((2 * k = Work.CORE4.nineP h ^ Work.CORE4.nineK h + 1 ∧
          2 * k' = Work.CORE4.nineP h ^ Work.CORE4.nineK h - 1) ∨
        (2 * k = Work.CORE4.nineP h ^ Work.CORE4.nineK h - 1 ∧
          2 * k' = Work.CORE4.nineP h ^ Work.CORE4.nineK h + 1)) ∧
      (h.D.M ⊓ B.H).relIndex h.D.M = Work.CORE4.nineP h ^ Work.CORE4.nineK h * k'
  -- the §4 (9) data for the canonical witness
  have hpodd : Odd (Work.CORE4.nineP h) := Work.CORE4.nineP_odd h
  have h7 : 7 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := Work.CORE4.nineP_seven h
  haveI : Fact (Work.CORE4.nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  obtain ⟨φ⟩ := Work.CORE4.nineP_iso h
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := Work.CORE4.nineP_le h
  have hm0 : Work.CORE4.nineK h ≠ 0 := by
    intro h0; rw [h0, pow_zero] at h7; omega
  have h2q : 2 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := by omega
  have hqodd : Odd (Work.CORE4.nineP h ^ Work.CORE4.nineK h) := hpodd.pow
  -- `t` as an element of `E = layerIn M`, and its image under `φ`
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact htE2
  -- `|C_E(t)| = 2 n`, `2n = q ± 1`
  obtain ⟨n, hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent (Work.CORE4.nineP h) (Work.CORE4.nineK h) hpodd
      (by omega : 5 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h) (φ ⟨B.t, htE⟩) ht'
  have hcardC : Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * n := by
    have h1 : Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf (Work.GW2.layerIn h.D.M)) =
        Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) := by
      rw [subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE]
    have h2 : Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) =
        Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))))) :=
      card_centralizer_singleton_map φ ⟨B.t, htE⟩
    have h3 : Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))))) = 2 * n := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    calc Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H)
        = Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf
            (Work.GW2.layerIn h.D.M)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ = Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
            Set ↥(Work.GW2.layerIn h.D.M))) := h1
      _ = Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
            Set (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))))) := h2
      _ = 2 * n := h3
  -- `S ≤ C_E(t)` and `4 ∣ |S| ≤ 2n`, whence `n` is even
  have hSK : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M ⊓ B.H := le_inf hSE B.S_le_H
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card ↥B.S0 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr B.S0_le, B.S0_index] at h
    exact h.symm
  have hS4 : 4 ∣ Nat.card ↥(B.S : Subgroup G) := by
    have h2 : 2 ∣ Nat.card ↥B.S0 := by
      have h := Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
      rwa [B.t_order] at h
    obtain ⟨c, hc⟩ := h2
    rw [hcardS, hc]
    exact ⟨c, by ring⟩
  have h4 : 4 ∣ 2 * n := by
    rw [← hcardC]
    exact dvd_trans hS4 (Subgroup.card_dvd_of_le hSK)
  have hnEven : Even n := by
    obtain ⟨s, hs⟩ := h4
    exact ⟨s, by omega⟩
  -- `relIndex · 2n = |PSL(2,q)|` and `2 |PSL(2,q)| = q (q² - 1)`
  have hrel := Work.GW2.Case2Ctx.relIndex_M_inter_H hbc h
  have hr : (Work.GW2.layerIn h.D.M ⊓ B.H).relIndex (Work.GW2.layerIn h.D.M) * (2 * n) =
      Nat.card (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))) := by
    have hmul := Subgroup.relIndex_mul_card (Work.GW2.layerIn h.D.M ⊓ B.H)
      (Work.GW2.layerIn h.D.M)
    rw [inf_eq_left.mpr inf_le_left, hcardC] at hmul
    rw [Nat.card_congr φ.toEquiv] at hmul
    exact hmul
  have hN : 2 * Nat.card (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))) =
      Work.CORE4.nineP h ^ Work.CORE4.nineK h *
        ((Work.CORE4.nineP h ^ Work.CORE4.nineK h) ^ 2 - 1) := by
    have hh := Work.PSL2.card_PSL2_galoisField (Work.CORE4.nineP h) (Work.CORE4.nineK h) hpodd hm0
    rw [show Work.CORE4.nineP h ^ (2 * Work.CORE4.nineK h) =
        (Work.CORE4.nineP h ^ Work.CORE4.nineK h) ^ 2 from by
      rw [← pow_mul, Nat.mul_comm (Work.CORE4.nineK h) 2]] at hh
    exact hh
  rcases hn with hn | hn
  · -- `2n = q - 1`: then `k := n` is even, `k' := n + 1` is odd, `2k' = q + 1`
    have hk' : 2 * (n + 1) = Work.CORE4.nineP h ^ Work.CORE4.nineK h + 1 := by omega
    have hodd : Odd (n + 1) := by
      obtain ⟨s, hs⟩ := hnEven
      exact ⟨s, by omega⟩
    refine ⟨n, n + 1, hqodd, h7, hnEven, hodd, Or.inr ⟨hn, hk'⟩, ?_⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inl ⟨hn, hk'⟩) hN hr
  · -- `2n = q + 1`: then `k := n` is even, `k' := n - 1` is odd, `2k' = q - 1`
    have hn1 : 1 ≤ n := by omega
    have hk' : 2 * (n - 1) = Work.CORE4.nineP h ^ Work.CORE4.nineK h - 1 := by omega
    have hodd : Odd (n - 1) := by
      obtain ⟨s, hs⟩ := hnEven
      exact ⟨s - 1, by omega⟩
    refine ⟨n, n - 1, hqodd, h7, hnEven, hodd, Or.inl ⟨hn, hk'⟩, ?_⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inr ⟨hn, hk'⟩) hN hr

end Work.CORE4
