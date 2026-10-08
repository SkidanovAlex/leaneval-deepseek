/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the numeric data of §4 (7)–(10) with §4 (7) removed from the critical path

`Work.CORE4.Case2Numeric_of_layer` produces the tuple of Bender's §4 from
`Case2SevenFacts B h.D` (§4 (7)) and `Case2EightAll B h.D` (§4 (8)), but the build reports that
its `hSeven` parameter is **never used**.  This file redoes the assembly with the §4 (7)
parameter dropped, and with §4 (8) reduced to exactly the two numerics the tuple needs
(`u ≤ p`, `3 ≤ p₀`), supplied by `hNu` (the statement delegated as `Work.CORE4.EightNuCtx`);
together with `¬ Case2InvNormal B h.D` the tuple is then complete.

The remaining input is `hS0 : B.S0 ≤ C_G(B.U)`, i.e. `[S₀, U] = 1` (Bender p. 227:
`S₀ = C_S(U)`), which `Work.CORE4.S0CentU_of_O2` + `Work.CORE4.SevenO2HM` supply and which
`Work.CORE4.Case2NotInvNormal` turns into `¬ Case2InvNormal`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2NotInvNormal
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.Case2Numeric
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2EightAllOfCtx
import Submission.Work.CORE4.S0CentUO2

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Bender §4 (8), pp. 225–226, at the `Case2Ctx` level, in the form the tuple needs:
unless `I_U(s) ⊴ Ĥ`, `u = |U : N_U(A)| ≤ p` and `3 ≤ p₀ = |N_U(A) : N_U(P)|`.
(Delegated as `Work.CORE4.EightNuCtx`.) -/
def EightNuCtxProp (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
      ¬ Work.GW2.Case2InvNormal B h.D →
      ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        Work.GW2.Case2EightU B A ≤ p ∧ 3 ≤ Work.GW2.Case2EightP0 B P A

/-- **The numeric data of §4, without §4 (7) and without the §4 (8) dichotomy.**

Given `[S₀, U] = 1` (Bender p. 227) and the two §4 (8) numerics `u ≤ p`, `3 ≤ p₀` (Bender
pp. 225–226, `EightNuCtxProp`), the §4 configuration produces the tuple of Bender's §4 (10):
`q = qOf h`, `k, k'` with `{2k, 2k'} = {q ± 1}`, `|M : M ⊓ H| = q k'`, `k = |K| |S₀|`,
`p = |F|.minFac`, `P ≤ F` of order `p`, `A` the unique `(p,p)`-subgroup of `F ⊔ K` containing `P`,
`u = Case2EightU B A`, `p₀ = Case2EightP0 B P A`, `p₁ = Case2EightP1 P A`, and all the
inequalities `3 ≤ p₀`, `p₀` odd, `p₀ ≤ p₁ ≤ p + 1`, `p₀ ≤ p`, `2p ≤ k`, `1 ≤ u ≤ p`, together with
`|H : H ⊓ M| = u p₀` and Bender's (2) `B₀ ≤ C_G(S)`.

This is a drop-in replacement for `Case2NumericImpl` once `hS0` and `hNu` are available; the whole
π-layer of §4 (7) is not used. -/
theorem Case2Numeric_of_ctx (I : Work.GW2.C4Inputs) (hNu : EightNuCtxProp I) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) →
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          q = qOf h ∧ Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          Work.GW2.Case2EightObj h.D p P A ∧
          u = Work.GW2.Case2EightU B A ∧ p0 = Work.GW2.Case2EightP0 B P A ∧
          p1 = Work.GW2.Case2EightP1 P A ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  intro G _ _ hbc B h hS0
  -- §4 (9)/(10): the canonical `q = qOf h` and `k, k'`
  obtain ⟨k, k', hqodd, hq7, hkeven, hk'odd, hcases, hrelMH⟩ := Case2ParityQOf G I hbc B h
  -- the prime `p` and `P ≤ F` of order `p`
  obtain ⟨hpprime, -, P, hPF, hPcard⟩ := Case2Fill G B h
  -- the `(p,p)`-subgroup `A` (§4 (8) object layer; no §4 (7) needed)
  obtain ⟨A, hObj⟩ := ctxObjExists I hbc B h (Nat.card ↥h.D.F).minFac P hpprime hPF hPcard
  -- the elementary §4 (8) conjuncts
  obtain ⟨hpK0, -, hNP, hNPA, hp0odd, hp0p1, hp1p, hp0p⟩ :=
    ctxEightElemFacts I hbc B h (Nat.card ↥h.D.F).minFac P A hpprime hPF hPcard hObj
  have hpK : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.K :=
    hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)
  -- §4 (9): `k = |K| · |S₀|`
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Case2KmulS0 G I hbc B h (qOf h) k k' hqodd hq7 hcases hrelMH
  -- Bender's exceptional case of (8) is excluded
  have hInv : ¬ Work.GW2.Case2InvNormal B h.D := Case2NotInvNormal G I hbc B h hS0
  -- §4 (8) proper: `u ≤ p` and `3 ≤ p₀`
  obtain ⟨hup, hp03⟩ :=
    hNu G hbc B h hInv (Nat.card ↥h.D.F).minFac P A hpprime hPF hPcard hObj
  -- Bender's (2): `B₀ ≤ C_G(S)`
  have hB0S : h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
    have hpre : Work.GW2.Case2PrePlus B h.D := Case2PrePlusOfCtx G I hbc B h
    have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
    rw [hpre.2.2]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    exact le_inf le_rfl hSE
  refine ⟨qOf h, k, k', (Nat.card ↥h.D.F).minFac, P, A, Work.GW2.Case2EightU B A,
    Work.GW2.Case2EightP0 B P A, Work.GW2.Case2EightP1 P A, rfl, hqodd, hq7, hkeven, hk'odd,
    hcases, hrelMH, hkK, hpK, hObj, rfl, rfl, rfl, ?_, hB0S,
    hp03, hp0odd, hp0p1, hp1p, hp0p, Case2Num_two_p_le_k B h hkK hpK,
    Case2Num_one_le_relIndex B A, hup⟩
  -- `|H : H ⊓ M| = u · p₀`
  simpa only [Work.GW2.Case2EightU, Work.GW2.Case2EightP0] using
    Case2Num_MH_relIndex I B h P A hNP hNPA

/-- The same, in the packaged shape of `Work.CORE4.Case2NumericImpl` (which is what the assembly
`Work.CORE4.Case2CountImpl_of_pieces` consumes), with the `S₀ ≤ C_G(U)` input kept explicit. -/
theorem Case2NumericImpl_of_ctx (I : Work.GW2.C4Inputs) (hNu : EightNuCtxProp I) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) →
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          q = qOf h ∧ Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
          A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
          (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
              (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
          u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
          p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
                 (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
          p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  intro G _ _ hbc B h hS0
  obtain ⟨q, k, k', p, P, A, u, p0, p1, hq, hqodd, hq7, hkeven, hk'odd, hcases, hrelMH, hkK, hpK,
    hObj, hu, hp0, hp1, hHrel, hB0S, hp03, hp0odd, hp0p1, hp1p, hp0p, h2p, hu1, hup⟩ :=
    Case2Numeric_of_ctx I hNu G hbc B h hS0
  obtain ⟨hpprime, hPF, hPcard, hAle, hAcard, hAexp, hPAsub, hAuniq⟩ := hObj
  exact ⟨q, k, k', p, P, A, u, p0, p1, hq, hqodd, hq7, hkeven, hk'odd, hcases, hrelMH, hkK,
    hpK, hpprime, hPF, hPcard, hAle, hAcard, hAexp, hPAsub, hAuniq, hu, hp0, hp1, hHrel, hB0S,
    hp03, hp0odd, hp0p1, hp1p, hp0p, h2p, hu1, hup⟩


/-- **`Case2NumericImpl I` from the §4 (8) numerics alone.**

`hS0 : B.S0 ≤ C_G(B.U)` is now unconditional
(`Work.CORE4.S0CentU_of_ctx` = `Case2S0_comm_U` + `SevenO2HM`), so the only remaining input is
`EightNuCtxProp I`, i.e. Bender's §4 (8) numerics `u ≤ p`, `3 ≤ p₀`. -/
theorem Case2NumericImpl_of_ctx' (I : Work.GW2.C4Inputs) (hNu : EightNuCtxProp I) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          q = qOf h ∧ Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
          A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
          (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
              (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
          u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
          p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
                 (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
          p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p :=
  fun G _ _ hbc B h => Case2NumericImpl_of_ctx I hNu G hbc B h (S0CentU_of_ctx I hbc h)

end Work.CORE4
