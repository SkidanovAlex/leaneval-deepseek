/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the §4 counting leaf, reduced to Bender's (12) alone

This module assembles `Work.GW2.Case2CountImpl` from

* `EightNuCtxProp I` — Bender §4 (8), pp. 225–226: `u = |U : N_U(A)| ≤ p` and
  `3 ≤ p₀ = |N_U(A) : N_U(P)|` unless `I_U(s) ⊴ Ĥ` (delegated as `Work.CORE4.EightNuCtx`); and
* `Case2LBImpl I` — Bender §4 (12), p. 227:
  `(p₁ − 1) q k' ((p₁ − 1)(q k' − 1) − q(q−1)/p) ≤ |G : M|`.

The §4 (7) layer is *not* used (see `Submission/Work/CORE4/NOTES_CASE2COUNT.md` §5): the numeric
data comes from `Work.CORE4.Case2Numeric_of_ctx`, which drops the (dead) `hSeven` parameter of
`Work.CORE4.Case2Numeric_of_layer`; the only role §4 (7) played — the identity `O₂(H ⊓ M) = O₂(H)`,
needed to get `[S₀, U] = 1` and hence `¬ Case2InvNormal` — is `Work.CORE4.SevenO2HM` +
`Work.CORE4.S0CentU_of_ctx`.

Everything else is proved in the workspace: §4 (10) is `Work.CORE4.Case2UpperBoundImpl_proof`, the
`BGData` input is `Work.CORE4.Case2BGK`, and the final arithmetic is `Work.GW2.case2Arith`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Arith
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2BGK
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.NumericOfCtx
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.ConjSubgroupCount

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Bender §4 (12), p. 227: `|G : M|` is at least
`(p₁ − 1) q k' ((p₁ − 1)(q k' − 1) − q(q−1)/p)`, where `p₁ = #{X ≤ A : X ~ P}` and
`q = qOf h`, `k, k'` are the halves of `q ± 1` (`k` even, `k'` odd) with `k = |K| |S₀|`.

Since `|G : M| = #conj(P)` (`Work.CORE4.Case2NormalizerP` + `Work.CORE4.ConjSubgroupCount`), this
is Bender's count of the conjugates of `P`. -/
def Case2LBImpl (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G) (p1 : ℕ),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      A ≤ h.D.F ⊔ h.D.K → Nat.card ↥A = p ^ 2 → (∀ x ∈ A, x ^ p = 1) → P ≤ A →
      (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
          (∀ x ∈ B', x ^ p = 1) → B' = A) →
      p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      (((qOf h : ℚ) * k' * ((p1 : ℚ) - 1) * ((qOf h : ℚ) * k')) *
          (((p1 : ℚ) - 1) * ((qOf h : ℚ) * k' - 1) -
            ((qOf h : ℚ) - 1) * qOf h / p))
        ≤ ((qOf h * k' * h.D.M.index : ℕ) : ℚ)

/-- **Bender §4 (7)–(12) from §4 (8) and (12).**  The lower bound of (12) is multiplied by
`q k'` and compared with (10); the resulting inequality is Bender's (12), whose negation is the
proved pure arithmetic `Work.GW2.case2Arith`. -/
theorem Case2CountImpl_of_pieces2 (I : Work.GW2.C4Inputs)
    (hNu : EightNuCtxProp I) (hLB : Case2LBImpl I) :
    Work.GW2.Case2CountImpl I := by
  intro G _ _ hbc B h2 h
  obtain ⟨q, k, k', p, P, A, u, p0, p1, hq, hqodd, hq7, hkeven, hk'odd, hcases, hrelMH, hkK,
    hpK, hp, hPF, hPcard, hAle, hAcard, hAexp, hPAsub, hAuniq, hu, hp0, hp1, hHrel, hB0S,
    hp03, hp0odd, hp0p1, hp1p, hp0p, h2p, hu1, hup⟩ :=
    Case2NumericImpl_of_ctx' I hNu G hbc B h
  -- normalise `q` to the canonical field order `qOf h`
  subst hq
  -- Bender–Glauberman's `BGData` with `D.k ≤ k u p₀` (§4 (10))
  obtain ⟨D, hDS, hDS0, hDt, hDk⟩ := Case2BGK G I hbc B h k u p0 hkK hHrel hB0S
  have hUB := Case2UpperBoundImpl_proof I G hbc B h (qOf h) k k' u p0 D hDS hDS0 hDt hDk
    hqodd hq7 hkeven hrelMH hHrel hu1 hp03
  -- Bender §4 (12), lower bound
  have hpK0 : p ∣ Nat.card ↥h.D.K0 := by
    rw [← hPcard]
    exact (Subgroup.card_dvd_of_le hPF).trans (card_F_dvd_card_K0_of_ctx I hbc B h)
  have hLB' := hLB G hbc B h k k' p P A p1 hkeven hk'odd hcases hkK hp hPF hPcard hAle hAcard
    hAexp hPAsub hAuniq hp1 hqodd hq7 hpK0 hrelMH
  -- (12) combined with (10): `q k' · LB ≤ q k' |G : M| < 6 k² u³ p₀³`
  have h12 : (((qOf h : ℚ) * k' * ((p1 : ℚ) - 1) * ((qOf h : ℚ) * k')) *
      (((p1 : ℚ) - 1) * ((qOf h : ℚ) * k' - 1) - ((qOf h : ℚ) - 1) * qOf h / p)) ≤
      6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 := le_of_lt (lt_of_le_of_lt hLB' hUB)
  exact (Work.GW2.case2Arith (qOf h) k k' p p0 p1 u hq7 hqodd hcases hkeven hp hp03 hp0odd
    hp0p1 hp1p hp0p h2p hu1 hup h12).elim


/-- Bender's §4 (12) count of the conjugates of `P` (delegated as
`Work.CORE4.Counting.ConjCount12`). -/
def ConjCount12Prop (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
      (P A : Subgroup G) (p1 : ℕ),
      Even k → Odd k' →
      ((2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
        (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1)) →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      A ≤ h.D.F ⊔ h.D.K → Nat.card ↥A = p ^ 2 → (∀ x ∈ A, x ^ p = 1) → P ≤ A →
      (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
          (∀ x ∈ B', x ^ p = 1) → B' = A) →
      p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard →
      Odd (qOf h) → 7 ≤ qOf h → p ∣ Nat.card ↥h.D.K0 →
      (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k' →
      (((qOf h : ℚ) * k' * ((p1 : ℚ) - 1) * ((qOf h : ℚ) * k')) *
          (((p1 : ℚ) - 1) * ((qOf h : ℚ) * k' - 1) -
            ((qOf h : ℚ) - 1) * qOf h / p))
        ≤ ({X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P}.ncard : ℚ)

/-- `Case2LBImpl` from `ConjCount12Prop`, using `#conj(P) = |G : M|` (`Case2NormalizerP` +
`ConjSubgroupCount`) and `1 ≤ q k'`. -/
theorem Case2LB_of_conjCount (I : Work.GW2.C4Inputs) (hCount : ConjCount12Prop I) :
    Case2LBImpl I := by
  intro G _ _ hbc B h k k' p P A p1 hkeven hk'odd hcases hkK hp hPF hPcard hAle hAcard hAexp
    hPAsub hAuniq hp1 hqodd hq7 hpK0 hrelMH
  have hc := hCount G hbc B h k k' p P A p1 hkeven hk'odd hcases hkK hp hPF hPcard hAle hAcard
    hAexp hPAsub hAuniq hp1 hqodd hq7 hpK0 hrelMH
  -- `P ≠ ⊥`
  have hPne : P ≠ ⊥ := by
    intro hbot
    have : Nat.card ↥P = 1 := by rw [hbot, Subgroup.card_bot]
    have hp2 : 2 ≤ p := hp.two_le
    omega
  -- `#conj(P) = |G : M|`
  have hcard : ({X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P}.ncard : ℚ) =
      (h.D.M.index : ℚ) := by
    have h1 : ({X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P}).ncard =
        (Subgroup.normalizer (P : Set G)).index := ConjSubgroupCount G P
    rw [h1, Case2NormalizerP G B h P hPF hPne]
  rw [hcard] at hc
  -- `|G : M| ≤ q k' |G : M|`
  have hq7' : 7 ≤ qOf h := nineP_seven h
  have hpos : 0 < qOf h * k' := by
    have h1 : 0 < qOf h := by omega
    have h2 : 0 < k' := by rcases hcases with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    exact Nat.mul_pos h1 h2
  have hle : h.D.M.index ≤ qOf h * k' * h.D.M.index := Nat.le_mul_of_pos_left _ hpos
  have hle' : (h.D.M.index : ℚ) ≤ ((qOf h * k' * h.D.M.index : ℕ) : ℚ) := by
    exact_mod_cast hle
  exact le_trans hc hle'

/-- **`Work.GW2.Case2CountImpl I` from the `§4 (8)` numerics and Bender's `(12)`. -/
theorem Case2CountImpl_of_pieces3 (I : Work.GW2.C4Inputs)
    (hNu : EightNuCtxProp I) (hCount : ConjCount12Prop I) :
    Work.GW2.Case2CountImpl I :=
  Case2CountImpl_of_pieces2 I hNu (Case2LB_of_conjCount I hCount)

end Work.CORE4
