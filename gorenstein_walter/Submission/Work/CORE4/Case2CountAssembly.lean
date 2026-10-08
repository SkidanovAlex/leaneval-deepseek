/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# AREA CORE4 — assembly of Bender §4 (7)–(12) from four named pieces

This module reduces the leaf `Work.CORE4.Case2Count` to four statements, each of which is the
precise content of one stretch of Bender 1981, §4, pp. 225–228:

* `Case2Numeric` (Bender's (7)–(8) and p. 225): the numbers `q, k, k', p`, the subgroups
  `P ≤ F` and `A ≤ F·K` (the unique `(p,p)`-subgroup), `u, p₀, p₁`, the parity data of (10), the
  identity `k = |K|·|S₀|`, `p ∣ |K|`, `|H : H ⊓ M| = u·p₀` and `q = qOf h` (the canonical field
  order of §4 (9));
* `Case2BGK` (the input of Bender–Glauberman's Theorem A): a `BGData` with `S`, `S₀`, `t` of the
  configuration and Bender–Glauberman's `k` equal to `k·u·p₀`;
* `Case2UpperBound` (Bender's (10)): `q k' |G : M| < 6 k² u³ p₀³`;
* `Case2LowerBound` (Bender's (11)–(12)): the number `|G : M|` of conjugates of `P` is at least
  `(p₁ − 1) q k' ((p₁ − 1)(q k' − 1) − (q − 1)q/p)`.

Multiplying the lower bound by `q k'` and comparing with (10) gives Bender's (12), which the
proved pure arithmetic `Work.GW2.case2Arith` rules out; this is `Case2CountImpl_of_pieces` below.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Arith
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2NormalizerP

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## 1. The canonical field order `q` of §4 (9) -/

section Nine

variable {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}

/-- The prime `pField` of the isomorphism `E(M) ≅ L₂(pField^kField)` of §4 (9), chosen once. -/
noncomputable def nineP (h : Work.GW2.Case2Ctx B) : ℕ := Classical.choose h.nine

/-- The exponent `kField` of §4 (9). -/
noncomputable def nineK (h : Work.GW2.Case2Ctx B) : ℕ :=
  Classical.choose (Classical.choose_spec h.nine)

/-- Bender's field order `q = pField ^ kField` of §4 (9). -/
noncomputable def qOf (h : Work.GW2.Case2Ctx B) : ℕ := nineP h ^ nineK h

/-- `pField` is prime. -/
theorem nineP_prime (h : Work.GW2.Case2Ctx B) : (nineP h).Prime :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec h.nine))).out

/-- `pField` is odd. -/
theorem nineP_odd (h : Work.GW2.Case2Ctx B) : Odd (nineP h) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h.nine))).1

/-- `q = pField ^ kField` is at least `7`. -/
theorem nineP_seven (h : Work.GW2.Case2Ctx B) : 7 ≤ qOf h :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h.nine))).2.1

/-- §4 (9): `E(M) ≅ L₂(q)`. -/
theorem nineP_iso (h : Work.GW2.Case2Ctx B) [Fact (nineP h).Prime] :
    Nonempty (Work.GW2.layerIn h.D.M ≃* PSL(2, GaloisField (nineP h) (nineK h))) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h.nine))).2.2.1

/-- §4 (9): `S ≤ E(M)`. -/
theorem nineP_le (h : Work.GW2.Case2Ctx B) :
    (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h.nine))).2.2.2

end Nine

/-! ## 2. The four pieces -/

/-- Bender §4 (7)–(8) and the objects of p. 225: the numeric data of the §4 configuration. -/
def Case2NumericImpl (I : Work.GW2.C4Inputs) : Prop :=
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
        3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p

/-- The input of Bender–Glauberman's Theorem A (§4 (10)): a `BGData` compatible with Bender's
`S`, `S₀`, `t` whose `k` is Bender–Glauberman's `k`, which Bender p. 227 identifies with
`k·u·p₀`. -/
def Case2BGKImpl (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k u p0 : ℕ),
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
      (h.D.M ⊓ B.H).relIndex B.H = u * p0 →
      h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) →
      ∃ D : Work.GW2.BGData G,
        D.S = B.S ∧ D.S0 = B.S0 ∧ D.t = B.t ∧ D.k ≤ k * u * p0

/-- Bender §4 (10). -/
def Case2UpperBoundImpl (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
      (q k k' u p0 : ℕ) (D : Work.GW2.BGData G),
      D.S = B.S → D.S0 = B.S0 → D.t = B.t → D.k ≤ k * u * p0 →
      Odd q → 7 ≤ q → Even k →
      (h.D.M ⊓ B.H).relIndex h.D.M = q * k' →
      (h.D.M ⊓ B.H).relIndex B.H = u * p0 →
      1 ≤ u → 3 ≤ p0 →
      ((q * k' * h.D.M.index : ℕ) : ℚ) < 6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3

/-- Bender §4 (10), proved: `I.bgA` (Theorem A of Bender–Glauberman) with `D.k ≤ k·u·p₀` and the
two index identities.  The hypotheses `1 ≤ u`, `3 ≤ p₀` (which come from §4 (7)–(8)) make `u·p₀`
positive, which is what lets BG's inequality be multiplied by `u·p₀`. -/
theorem Case2UpperBoundImpl_proof (I : Work.GW2.C4Inputs) : Case2UpperBoundImpl I := by
  intro G _ _ hbc B h q k k' u p0 D hDS hDS0 hDt hDk hqodd hq7 hk hrel hHrel hu1 hp03
  -- `D.H = C_G(t) = B.H`, since `D.t = B.t`.
  have hHH : D.H = B.H := by
    show Subgroup.centralizer ({D.t} : Set G) = Subgroup.centralizer ({B.t} : Set G)
    rw [hDt]
  -- Bender–Glauberman, Theorem A, for the `BGData` `D`: `|G : H| < 6 k_BG² ≤ 6 (k u p₀)²`.
  have hbg' : B.H.index < 6 * (k * u * p0) ^ 2 := by
    rw [← hHH]
    calc D.H.index < 3 * (2 * D.k ^ 2) := (I.bgA G D).1
      _ = 6 * D.k ^ 2 := by ring
      _ ≤ 6 * (k * u * p0) ^ 2 := Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left hDk 2)
  have hupos : 0 < u * p0 := Nat.mul_pos (by omega) (by omega)
  have hmain : u * p0 * B.H.index < u * p0 * (6 * (k * u * p0) ^ 2) :=
    Nat.mul_lt_mul_of_pos_left hbg' hupos
  have hsimp : u * p0 * (6 * (k * u * p0) ^ 2) = 6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by ring
  -- `|G : M ⊓ H|` computed in two ways (second isomorphism theorem / index multiplicativity).
  have hidx1 : (h.D.M ⊓ B.H).relIndex h.D.M * h.D.M.index = (h.D.M ⊓ B.H).index :=
    Subgroup.relIndex_mul_index (inf_le_left : h.D.M ⊓ B.H ≤ h.D.M)
  have hidx2 : (h.D.M ⊓ B.H).relIndex B.H * B.H.index = (h.D.M ⊓ B.H).index :=
    Subgroup.relIndex_mul_index (inf_le_right : h.D.M ⊓ B.H ≤ B.H)
  -- Bender §4 (10): `q k' |G : M| = u p₀ |G : H|`.
  have hEq : q * k' * h.D.M.index = u * p0 * B.H.index := by
    rw [hrel] at hidx1
    rw [hHrel] at hidx2
    exact hidx1.trans hidx2.symm
  have hfinal : q * k' * h.D.M.index < 6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by
    rw [← hsimp, hEq]
    exact hmain
  exact_mod_cast hfinal

/-- Bender §4 (11)–(12), lower bound. -/
def Case2LowerBoundImpl (I : Work.GW2.C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
      (pF kF : ℕ) [hpF : Fact pF.Prime] (q k k' p : ℕ) (P A : Subgroup G) (p1 : ℕ),
      Odd pF → 7 ≤ pF ^ kF → q = pF ^ kF →
      Nonempty (Work.GW2.layerIn h.D.M ≃* PSL(2, GaloisField pF kF)) →
      Odd q → 7 ≤ q → Even k → Odd k' →
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) →
      (h.D.M ⊓ B.H).relIndex h.D.M = q * k' →
      p ∣ k → k = Nat.card ↥h.D.K * Nat.card ↥B.S0 → p ∣ Nat.card ↥h.D.K →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      A ≤ h.D.F ⊔ h.D.K → Nat.card ↥A = p ^ 2 → (∀ x ∈ A, x ^ p = 1) → P ≤ A →
      (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
          (∀ x ∈ B', x ^ p = 1) → B' = A) →
      p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard →
      ((p1 - 1) * q * k' *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        (h.D.M.index : ℚ))

/-! ## 3. Assembly: (10) and (12) together contradict the arithmetic -/

/-- **Bender §4 (7)–(12), from the four pieces.** The lower bound of (12) is multiplied by
`q k'` and compared with (10); the resulting inequality is Bender's (12), whose negation is the
proved pure arithmetic `Work.GW2.case2Arith`. -/
theorem Case2CountImpl_of_pieces (I : Work.GW2.C4Inputs)
    (hNum : Case2NumericImpl I) (hBGK : Case2BGKImpl I)
    (hLB : Case2LowerBoundImpl I) :
    Work.GW2.Case2CountImpl I := by
  intro G _ _ hbc B h2 h
  obtain ⟨q, k, k', p, P, A, u, p0, p1, hqeq, hqodd, hq7, hk, hk', hdisj, hrel, hkK, hpK,
    hp, hPF, hPcard, hAle, hAcard, hApow, hPA, huniq, hu, hp0def, hp1def, hHrel,
    hB0S, hp03, hp0odd, hp01, hp1le, hp0p, h2p, hu1, hup⟩ := hNum G hbc B h
  -- the §4 (9) data, in the canonical normalization used by `qOf`
  haveI : Fact (nineP h).Prime := ⟨nineP_prime h⟩
  have hpFodd := nineP_odd (B := B) h
  have hpF7 := nineP_seven (B := B) h
  obtain ⟨φ⟩ := nineP_iso (B := B) h
  have hpk : p ∣ k := hkK ▸ dvd_mul_of_dvd_left hpK (Nat.card ↥B.S0)
  -- the Bender–Glauberman data
  obtain ⟨D, hDS, hDS0, hDt, hDk⟩ := hBGK G hbc B h k u p0 hkK hHrel hB0S
  have hUB' := Case2UpperBoundImpl_proof I G hbc B h q k k' u p0 D hDS hDS0 hDt hDk hqodd hq7
    hk hrel hHrel hu1 hp03
  have hLB' := hLB G hbc B h (nineP h) (nineK h) q k k' p P A p1 hpFodd hpF7 hqeq ⟨φ⟩
    hqodd hq7 hk hk' hdisj hrel hpk hkK hpK hp hPF hPcard hAle hAcard hApow hPA huniq hp1def
  -- multiply the lower bound by `q k' ≥ 0` and combine with (10)
  have hp1ge : 1 ≤ p1 := by omega
  have hp1c : ((p1 - 1 : ℕ) : ℚ) = (p1 : ℚ) - 1 := by
    rw [Nat.cast_sub hp1ge]; simp
  have hqk' : (0 : ℚ) ≤ (q : ℚ) * k' := by positivity
  have hmul := mul_le_mul_of_nonneg_left hLB' hqk'
  have hcast : ((q : ℚ) * k') * (h.D.M.index : ℚ) = ((q * k' * h.D.M.index : ℕ) : ℚ) := by
    push_cast; ring
  rw [hcast] at hmul
  have hbound : (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
      (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p)) <
      6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 := by
    have hb2 : ((q : ℚ) * k') * (((p1 : ℚ) - 1) * (q : ℚ) * k' *
        (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p)) <
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 := lt_of_le_of_lt hmul hUB'
    convert hb2 using 1
    ring
  have h12 : (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
      (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p)) ≤
      6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 := le_of_lt hbound
  exact (Work.GW2.case2Arith q k k' p p0 p1 u hq7 hqodd hdisj hk hp hp03 hp0odd hp01 hp1le
    hp0p h2p hu1 hup h12).elim

end Work.CORE4
