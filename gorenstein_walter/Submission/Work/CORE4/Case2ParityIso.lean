/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# AREA CORE4 — `Case2ParityIso`: the parity data *together with* the `L₂(q)` identification

`Case2Parity` (Bender §4 (10), parity refinement of `Case2RelIndexMH`) produces numbers `q, k, k'`
with `q` an odd prime power `≥ 7`, `k` even, `k'` odd, `{2k, 2k'} = {q ± 1}` and
`|M : M ⊓ H| = q k'`.  What the counting arguments downstream need is the *same* statement with the
field order `q` **tied to the isomorphism** `E(M) ≅ L₂(q)` supplied by `Case2Ctx.nine` (i.e. the
witness `(pF, kF)` of the `PSL(2, GaloisField pF kF)` structure is the very one appearing in
`q = pF ^ kF`), together with the exposed internal cardinality `|E(M) ⊓ H| = 2k`.

The proof is the one of `Case2Parity` with the witness `(p, m, φ)` of `h.nine` bound explicitly at
the top (rather than existentially quantified away), so that the field order `q = p ^ m` is the one
of `φ`, and with the computation `|E(M) ⊓ H| = |C_E(t)| = 2n` (whence `k = n`) exposed in the
statement.  The parity argument is unchanged: `S ≤ C_E(t)`, `4 ∣ |S| ≤ 2n` forces `n` even, so the
even half of `q ∓ 1` is `n = k` and the odd one is `k' = n ± 1`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.PSL2.Card

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-- Bender §4 (10), with the field order (`pF ^ kF`) tied to the isomorphism
`E(M) ≅ L₂(pF ^ kF)` of §4 (9) and with the internal cardinality `|E(M) ⊓ H| = 2k` exposed:
there are `φ : E(M) ≃* PSL(2, GaloisField pF kF)`, `k` even and `k'` odd with
`{2k, 2k'} = {pF ^ kF ± 1}`, `|M : M ⊓ H| = pF ^ kF · k'` and `|E(M) ⊓ H| = 2k`. -/
theorem Case2ParityIso (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (pF kF : ℕ) (_ : Fact pF.Prime)
          (φ : ↥(Work.GW2.layerIn h.D.M) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) (k k' : ℕ),
          Odd pF ∧ 7 ≤ pF ^ kF ∧ Even k ∧ Odd k' ∧
          ((2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
            (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = pF ^ kF * k' ∧
          Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * k := by
  intro G _ _ hbc B h
  classical
  -- the §4 (9) isomorphism, bound explicitly so that `q = p ^ m` is the field order of `φ`
  obtain ⟨p, m, hp, hpodd, h7, ⟨φ⟩, hSE⟩ := h.nine
  haveI := hp
  have hm0 : m ≠ 0 := by rintro rfl; rw [pow_zero] at h7; omega
  have h2q : 2 ≤ p ^ m := by omega
  have hqodd : Odd (p ^ m) := hpodd.pow
  -- `t` as an element of `E = layerIn M`, and its image under `φ`
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact htE2
  -- `|C_E(t)| = 2 n`, `2n = q ± 1`
  obtain ⟨n, hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent p m hpodd (by omega : 5 ≤ p ^ m) (φ ⟨B.t, htE⟩) ht'
  have hcardC : Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * n := by
    have h1 : Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf (Work.GW2.layerIn h.D.M)) =
        Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) := by
      rw [subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE]
    have h2 : Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) =
        Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField p m)))) :=
      card_centralizer_singleton_map φ ⟨B.t, htE⟩
    have h3 : Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField p m)))) = 2 * n := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    calc Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H)
        = Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf
            (Work.GW2.layerIn h.D.M)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ = Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
            Set ↥(Work.GW2.layerIn h.D.M))) := h1
      _ = Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
            Set (PSL(2, GaloisField p m)))) := h2
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
      Nat.card (PSL(2, GaloisField p m)) := by
    have hmul := Subgroup.relIndex_mul_card (Work.GW2.layerIn h.D.M ⊓ B.H)
      (Work.GW2.layerIn h.D.M)
    rw [inf_eq_left.mpr inf_le_left, hcardC] at hmul
    rw [Nat.card_congr φ.toEquiv] at hmul
    exact hmul
  have hN : 2 * Nat.card (PSL(2, GaloisField p m)) = p ^ m * ((p ^ m) ^ 2 - 1) := by
    have hh := Work.PSL2.card_PSL2_galoisField p m hpodd hm0
    rw [show p ^ (2 * m) = (p ^ m) ^ 2 from by rw [← pow_mul, Nat.mul_comm m 2]] at hh
    exact hh
  rcases hn with hn | hn
  · -- `2n = q - 1`: then `k := n` is even, `k' := n + 1` is odd, `2k' = q + 1`
    have hk' : 2 * (n + 1) = p ^ m + 1 := by omega
    have hodd : Odd (n + 1) := by
      obtain ⟨s, hs⟩ := hnEven
      exact ⟨s, by omega⟩
    refine ⟨p, m, hp, φ, n, n + 1, hpodd, h7, hnEven, hodd, Or.inr ⟨hn, hk'⟩, ?_, hcardC⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inl ⟨hn, hk'⟩) hN hr
  · -- `2n = q + 1`: then `k := n` is even, `k' := n - 1` is odd, `2k' = q - 1`
    have hn1 : 1 ≤ n := by omega
    have hk' : 2 * (n - 1) = p ^ m - 1 := by omega
    have hodd : Odd (n - 1) := by
      obtain ⟨s, hs⟩ := hnEven
      exact ⟨s - 1, by omega⟩
    refine ⟨p, m, hp, φ, n, n - 1, hpodd, h7, hnEven, hodd, Or.inl ⟨hn, hk'⟩, ?_, hcardC⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inr ⟨hn, hk'⟩) hN hr

end Work.CORE4
