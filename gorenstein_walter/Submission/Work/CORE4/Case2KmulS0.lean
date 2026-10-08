import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2CHs
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2RelIndexMH
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.PSL2.Card

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

/-! ## The two arithmetic/structural inputs of `Case2KmulS0`

The numerical hypotheses of `Case2KmulS0` determine `k` uniquely (the product `q k'` is the
triangular number `q(q-1)/2` or `q(q+1)/2`, whose index is unique; the two crossed conjunctions
are impossible because `Odd q` would force `q = q₀ + 1` with `q` odd), and they force
`k = |E(M) ⊓ H| / 2`.  The remaining content — Bender p. 227, that this half is `|K| · |S₀|` — is
the imported `Work.CORE4.Case2EHcard`. -/

/-- `n ↦ n (n+1)` is injective on `ℕ` (the triangular numbers have a unique index). -/
theorem Case2KmulS0_tri_inj {a b : ℕ} (h : a * (a + 1) = b * (b + 1)) : a = b := by
  have hmono : StrictMono (fun n : ℕ => n * (n + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  exact hmono.injective h

/-- **The number `k` of Bender §4 is forced.**  If `(q,k,k')` and `(q₀,k₀,k₀')` both satisfy the
triangular-number relations `{2k,2k'} = {q±1}`, `{2k₀,2k₀'} = {q₀±1}` with `q, q₀` odd, and give
the same product `q k' = q₀ k₀'`, then `k = k₀`.  (No parity hypothesis on `k` is needed.) -/
theorem Case2KmulS0_unique {q k k' q0 k0 k0' : ℕ}
    (hq : Odd q) (hq7 : 7 ≤ q) (hq0 : Odd q0) (hq07 : 7 ≤ q0)
    (h : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1))
    (h0 : (2 * k0 = q0 + 1 ∧ 2 * k0' = q0 - 1) ∨ (2 * k0 = q0 - 1 ∧ 2 * k0' = q0 + 1))
    (hR : q * k' = q0 * k0') : k = k0 := by
  have key : q * (2 * k') = q0 * (2 * k0') := by
    have h2 : 2 * (q * k') = 2 * (q0 * k0') := by rw [hR]
    nlinarith [h2]
  have hq1 : 1 ≤ q := by omega
  have hq01 : 1 ≤ q0 := by omega
  have e1 : (q - 1) + 1 = q := Nat.sub_add_cancel hq1
  have e2 : (q0 - 1) + 1 = q0 := Nat.sub_add_cancel hq01
  rcases h with ⟨hk, hk'⟩ | ⟨hk, hk'⟩ <;> rcases h0 with ⟨hk0, hk0'⟩ | ⟨hk0, hk0'⟩
  · have hkey : (q - 1) * ((q - 1) + 1) = (q0 - 1) * ((q0 - 1) + 1) := by
      rw [hk', hk0'] at key
      rw [e1, e2, mul_comm (q - 1) q, mul_comm (q0 - 1) q0]
      exact key
    have : q - 1 = q0 - 1 := Case2KmulS0_tri_inj hkey
    omega
  · have hkey : (q - 1) * ((q - 1) + 1) = q0 * (q0 + 1) := by
      rw [hk', hk0'] at key
      rw [e1, mul_comm (q - 1) q]
      exact key
    have hqeq : q - 1 = q0 := Case2KmulS0_tri_inj hkey
    obtain ⟨a, ha⟩ := hq
    obtain ⟨b, hb⟩ := hq0
    omega
  · have hkey : q * (q + 1) = (q0 - 1) * ((q0 - 1) + 1) := by
      rw [hk', hk0'] at key
      rw [e2, mul_comm (q0 - 1) q0]
      exact key
    have hqeq : q = q0 - 1 := Case2KmulS0_tri_inj hkey
    obtain ⟨a, ha⟩ := hq
    obtain ⟨b, hb⟩ := hq0
    omega
  · have hkey : q * (q + 1) = q0 * (q0 + 1) := by
      rw [hk', hk0'] at key
      exact key
    have hqeq : q = q0 := Case2KmulS0_tri_inj hkey
    omega

/-- **The half `k` is pinned to `|E(M) ⊓ H|`.**  With the §4 notation, there are `q, k, k'` with
`q` an odd prime power `≥ 7`, `{2k,2k'} = {q+1,q-1}`, `|M : M ⊓ H| = q k'` and
`|E(M) ⊓ H| = 2k`.  This is `Case2Parity` with the internal cardinality computation
(`E(M) ≅ L₂(q)` and Lagrange) exposed; it is proved from `Case2RelIndexMH`,
`Case2Ctx.relIndex_M_inter_H` and `Work.PSL2.card_PSL2_galoisField`. -/
theorem Case2KmulS0_parityEH :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ q k k' : ℕ, Odd q ∧ 7 ≤ q ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * k := by
  intro G _ _ I hbc B h
  obtain ⟨p, m, k', hp, hpodd, h7, ⟨φ⟩, hk', hrel⟩ := Work.CORE4.Case2RelIndexMH G I hbc B h
  haveI := hp
  have hm0 : m ≠ 0 := by rintro rfl; rw [pow_zero] at h7; omega
  have hp0 : 0 < p := hp.out.pos
  have hqpos : 0 < p ^ m := pow_pos hp0 m
  set C : ℕ := Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) with hC
  have hcardE : 2 * Nat.card ↥(Work.GW2.layerIn h.D.M) = p ^ m * ((p ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv]
    have hh := Work.PSL2.card_PSL2_galoisField p m hpodd hm0
    rwa [show p ^ (2 * m) = (p ^ m) ^ 2 from by rw [← pow_mul, Nat.mul_comm m 2]] at hh
  have hrelE : (Work.GW2.layerIn h.D.M ⊓ B.H).relIndex (Work.GW2.layerIn h.D.M) = p ^ m * k' := by
    rw [← Work.GW2.Case2Ctx.relIndex_M_inter_H hbc h]
    exact hrel
  have hLag : C * (p ^ m * k') = Nat.card ↥(Work.GW2.layerIn h.D.M) := by
    have hh := Subgroup.relIndex_mul_card (Work.GW2.layerIn h.D.M ⊓ B.H) (Work.GW2.layerIn h.D.M)
    rw [inf_eq_left.mpr inf_le_left, hrelE] at hh
    rw [hC, mul_comm]
    exact hh
  have hkey : 2 * C * k' = (p ^ m) ^ 2 - 1 := by
    have h2 : (2 * C * k') * p ^ m = ((p ^ m) ^ 2 - 1) * p ^ m := by
      calc (2 * C * k') * p ^ m
          = 2 * (C * (p ^ m * k')) := by ring
        _ = 2 * Nat.card ↥(Work.GW2.layerIn h.D.M) := by rw [hLag]
        _ = p ^ m * ((p ^ m) ^ 2 - 1) := hcardE
        _ = ((p ^ m) ^ 2 - 1) * p ^ m := by ring
    exact Nat.eq_of_mul_eq_mul_right hqpos h2
  have hfac : (p ^ m) ^ 2 - 1 = (p ^ m + 1) * (p ^ m - 1) := by
    have := Nat.sq_sub_sq (p ^ m) 1
    simpa using this
  rcases hk' with hA | hB
  · have h2k' : 2 * k' = p ^ m + 1 := hA
    have h2k'pos : 0 < 2 * k' := by omega
    have hcp : C = p ^ m - 1 := by
      have h1 : (2 * k') * C = (2 * k') * (p ^ m - 1) := by
        rw [show (2 * k') * C = 2 * C * k' by ring, hkey, hfac]
        rw [← h2k']
      exact Nat.eq_of_mul_eq_mul_left h2k'pos h1
    refine ⟨p ^ m, k' - 1, k', hpodd.pow, h7, Or.inr ⟨?_, ?_⟩, hrel, ?_⟩
    · omega
    · omega
    · rw [hC] at hcp
      omega
  · have h2k' : 2 * k' = p ^ m - 1 := hB
    have h2k'pos : 0 < 2 * k' := by omega
    have hcp : C = p ^ m + 1 := by
      have h1 : (2 * k') * C = (2 * k') * (p ^ m + 1) := by
        rw [show (2 * k') * C = 2 * C * k' by ring, hkey, hfac]
        rw [← h2k']
        ring
      exact Nat.eq_of_mul_eq_mul_left h2k'pos h1
    refine ⟨p ^ m, k' + 1, k', hpodd.pow, h7, Or.inl ⟨?_, ?_⟩, hrel, ?_⟩
    · omega
    · omega
    · rw [hC] at hcp
      omega

/-- Bender 1981, §4 (9), the identity `k = |K| · |S₀|`.

Let `q` be the order of the field with `E(M) ≅ L₂(q)` (`Case2Ctx.nine`), let `k` be the *even*
half of `q ∓ 1` and `k'` the odd one, so that `|M : M ⊓ H| = q k'` holds
(``Work.CORE4.Case2Parity``/``Case2RelIndexMH``: `|E : C_E(t)| = q k'` with `|C_E(t)| = 2k`).
Bender p. 227 proves `k = |K| · |S₀|` (this is the identity that turns Theorem A of
Bender–Glauberman, `|G : H| < 6(2|H : C_H(s)|)²`, into `q k' |G : M| < 6 k² u³ p₀³`).

The statement below only refers to the *numerical* content: for any triple `(q, k, k')` with
`q ≥ 7` odd, `{2k, 2k'} = {q+1, q-1}` and `|M : M ⊓ H| = q k'`, the number `k` is forced and
equals `|K| · |S₀|`. -/
theorem Case2KmulS0 :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (q k k' : ℕ),
        Odd q → 7 ≤ q →
        ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) →
        (h.D.M ⊓ B.H).relIndex h.D.M = q * k' →
        k = Nat.card ↥h.D.K * Nat.card ↥B.S0 := by
  intro G _ _ I hbc B h q k k' hq hq7 hdisj hrel
  obtain ⟨q0, k0, k0', hq0, hq07, hdisj0, hrel0, hcard0⟩ := Case2KmulS0_parityEH G I hbc B h
  have hk : k = k0 := Case2KmulS0_unique hq hq7 hq0 hq07 hdisj hdisj0 (hrel.symm.trans hrel0)
  have hEH : Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * k := by rw [hcard0, hk]
  have hB := Case2EHcard G I hbc B h
  have : 2 * k = 2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) := by rw [← hEH, hB]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

end Work.CORE4
