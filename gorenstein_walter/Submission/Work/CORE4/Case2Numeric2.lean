/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `Case2Numeric2`, and the diagnosis of its hypothesis list

## What the file contains

* `Case2Numeric2_of_layer` — the *assembly* half of the target `Case2Numeric2`, **proved** here:
  every conjunct of the target follows from the §4 (7)/(8) object layer, the identity
  `k = |K|·|S₀|`, the exclusion of Bender's exceptional case of (8), Bender's (2) in the form
  `B₀ ≤ C_U(S)`, and Bender's (11) — supplied as hypotheses.
* small proved helpers of §4 (8)–(10) (`Case2N2_two_p_le_k`, `Case2N2_one_le_u`,
  `Case2N2_MH_relIndex`, `Case2N2_not_U_le_M`), restated here so that this module is
  self-contained.

## Diagnosis (2026-10-05): `Case2Numeric2` is under-hypothesised

The printed hypothesis list of `Case2Numeric2` is only

    BenderCtx G,   B : BenderSetup G,   h : Case2Ctx B   (and I : C4Inputs),

i.e. Bender's §4 (1)–(5) (as `Case2Pre`), §4 (6), and §4 (9) (as the `nine` field), and it asserts
the **§4 (7)–(11)** data of pp. 225–228 as *conclusions*.  That data is derived by Bender from an
object layer which the hypothesis list does not contain and which is *not* a consequence of it:

* §4 (1) `K = [S∩E, U∩M] = I_{U∩M}(s) ≠ 1` and §4 (2) `B₀ = C_{U∩M}(S∩E)`, together with the
  Sylow choice `S ∩ M ∈ Syl₂(M)` — the design's `Case2PrePlus`.  `Defs.lean` records that
  `Case2Pre` "dropped" (1) and (2) and that the Sylow condition is not implied by it; the area's
  `SixConj.lean` machine-checks that `D.K = ⊥` (hence `p ∤ |K|`, killing the target's conjunct
  `p ∣ Nat.card h.D.K`) is compatible with every conjunct of `Case2Data`/`Case2Pre`, the
  `s ∈ S₀ ⟹ s = t ⟹ K = ⊥` configuration being recorded there.
* §4 (7), §4 (8) (`Q = Ω₁(Z₂(O_p(U)))`, `p ∣ |K₀|`, the `(p,p)`-subgroup `A ≤ F·K`,
  `N_U(P) = U ⊓ M`, `3 ≤ p₀ ≤ p₁ ≤ p+1`, `u ≤ p`), i.e. the design's `Case2SevenFacts` and
  `Case2EightAll` (design pass 9, `_design_gw/Core9.lean`, `NOTES_LEAD_gw_design9.md` §1.3).
  `NOTES_CORE4.md` §6 records that two independent provers found the split of §4
  "under-hypothesised" for exactly this reason, and the design's replacement leaf
  `Case2NumericImpl9` ("RESTATE") adds `Case2PrePlus`, `Case2SevenFacts`, `Case2EightAll` as
  hypotheses — `Case2Numeric2` has none of them.
* Bender's (11) `#{X ≤ P·E : X ∈ conj_G(P)} = (p₁−1) q k' + 1` is a statement about the
  **`G`-fusion of `P` relative to `E`** (Bender p. 227).  Nothing in `BenderCtx`, `Case2Ctx`
  or `C4Inputs` relates the class of `P` inside `A ≤ F ⊔ K` (i.e. `p₁`) to its class inside
  `P·E`: the inputs `l2primeCount`, `l2torusNorm`, `l2normTwo` count subgroups of `L₂(q)` and
  carry no fusion information, and the structure used by the paper (p. 227: `K ≤ E` via
  `S ≤ E` and `S₀ = C_S(U)`, `M ⊓ P·E = P·K·S₀ = C_{P×E}(A)`, `C_{F(U)}(P) = F × K₁`) is not
  part of the hypothesis list.  The area's own diagnosis in `Case2LowerBound.lean` reaches the
  same conclusion and its fix `Case2LowerBound3.lean` carries (11) plus that structure as
  **hypotheses**.

**Fix.**  Restate with the object layer as hypotheses — the file
`Submission/Work/CORE4/Case2Numeric.lean` does this for the base conjuncts
(`Case2Numeric_of_layer`), and `Case2Numeric2_of_layer` below does it for *all* conjuncts of
`Case2Numeric2`, including `q = qOf h`, `B₀ ≤ C_U(S)` and (11).

## What this session delivered for the restated leaf

* `Work.CORE4.Case2ParityQOf` (`Submission/Work/CORE4/Case2ParityQOf.lean`, PROVED): §4 (10) with
  the canonical field order `q = qOf h` — `∃ k k', Odd qOf ∧ 7 ≤ qOf ∧ Even k ∧ Odd k' ∧
  {2k, 2k'} = {qOf ± 1} ∧ |M : M ⊓ H| = qOf · k'`.  This is the form `Case2NumericImpl` needs.
* `Work.CORE4.Case2QOfCanonical` (`Submission/Work/CORE4/Case2QOfCanonical.lean`, PROVED): the
  field order is well defined — any odd prime power `p^k ≥ 5` with
  `layerIn h.D.M ≃* PSL(2, GF p k)` equals `qOf h`.
* `Work.CORE4.Case2Numeric2_of_layer` (this file, PROVED): all of `Case2Numeric2` from the
  §4 (7)/(8) layer, `k = |K|·|S₀|`, `¬ Case2InvNormal`, `B₀ ≤ C_U(S)` and (11) as hypotheses.
* `Work.CORE4.Case2N2_two_p_le_k`, `Case2N2_one_le_u`, `Case2N2_MH_relIndex`,
  `Case2N2_not_U_le_M` (this file, PROVED): the arithmetic/index conjuncts of §4 (8)–(10).
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2CHs
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2BGData
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2ParityQOf

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Helper lemmas of §4 (8)–(10) (proved)

`Case2N2_not_U_le_M`, `Case2N2_two_p_le_k`, `Case2N2_one_le_u` and `Case2N2_MH_relIndex` are the
elementary (arithmetic/index) conjuncts of the target.  They are stated here rather than imported
from the in-flight `Submission/Work/CORE4/Case2Numeric.lean` so that this module is
self-contained. -/

/-- `U ⊄ M`: §4 (9) gives `S ≤ E(M) ≤ M`, so `U ≤ M` would force `H = U · S ≤ M`, contradicting
§4 (1).  Bender uses this to derive `3 ≤ p₀`. -/
theorem Case2N2_not_U_le_M (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) : ¬ B.U ≤ h.D.M := by
  intro hUM
  exact Work.GW2.Case2Pre.not_H_le B h.D h.pre
    ((Work.GW2.Case2Ctx.H_eq_U_sup_S I h).trans_le (sup_le hUM h.S_le_M))

/-- `2 * p ≤ k` when `k = |K| · |S₀|` and `p ∣ |K|`: `p ≤ |K|`, and `|S₀| ≥ 2` because `t ∈ S₀` is
an involution. -/
theorem Case2N2_two_p_le_k (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) {k p : ℕ}
    (hk : k = Nat.card ↥h.D.K * Nat.card ↥B.S0) (hp : p ∣ Nat.card ↥h.D.K) : 2 * p ≤ k := by
  have hpK : p ≤ Nat.card ↥h.D.K := Nat.le_of_dvd Nat.card_pos hp
  have hS0 : 2 ≤ Nat.card ↥B.S0 := by
    refine Nat.le_of_dvd Nat.card_pos ?_
    have h := Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
    rwa [B.t_order] at h
  rw [hk]
  calc 2 * p ≤ 2 * Nat.card ↥h.D.K := by omega
    _ = Nat.card ↥h.D.K * 2 := by ring
    _ ≤ Nat.card ↥h.D.K * Nat.card ↥B.S0 := Nat.mul_le_mul_left _ hS0

/-- `1 ≤ u` for `u = |U : N_U(A)|`: relative indices of subgroups are positive. -/
theorem Case2N2_one_le_u (B : Work.GW2.BenderSetup G) (A : Subgroup G) :
    1 ≤ (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U := by
  have h := Subgroup.relIndex_mul_card (B.U ⊓ Subgroup.normalizer (A : Set G)) (B.U)
  have hpos : 0 < Nat.card ↥(B.U : Subgroup G) := Nat.card_pos
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hzero : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U = 0 := by omega
  rw [hzero, Nat.zero_mul] at h
  omega

/-- §4 (10), the index identity `|H : H ⊓ M| = u · p₀`.

For `u = |U : N_U(A)|` and `p₀ = |N_U(A) : N_U(P)|`, relative-index multiplicativity along
`N_U(P) ≤ N_U(A) ≤ U` gives `p₀ · u = |U : N_U(P)|`; with `N_U(P) = U ⊓ M` (§4 (8)) and
`|H : H ⊓ M| = |U : U ⊓ M|` (`Case2Ctx.relIndex_H_inter_M`) this is the claim. -/
theorem Case2N2_MH_relIndex (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) {P A : Subgroup G}
    (hP : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M)
    (hPA : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    (h.D.M ⊓ B.H).relIndex B.H =
      (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
  have hkey := Subgroup.relIndex_mul_relIndex
    (H := B.U ⊓ Subgroup.normalizer (P : Set G))
    (K := B.U ⊓ Subgroup.normalizer (A : Set G)) (L := B.U)
    (le_inf inf_le_left hPA) inf_le_left
  have hkey' : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) =
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex B.U := by
    have hcomm : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
        (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
          (B.U ⊓ Subgroup.normalizer (A : Set G)) =
        (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
            (B.U ⊓ Subgroup.normalizer (A : Set G)) *
          (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U := Nat.mul_comm _ _
    rw [hcomm, hkey]
  have h1 : (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex B.U =
      (B.U ⊓ h.D.M).relIndex B.U := by rw [hP]
  rw [hkey', h1]
  exact Work.GW2.Case2Ctx.relIndex_H_inter_M I h

/-! ## The assembly of the target from the missing layer -/

/-- **`Case2Numeric2`, assembled from the §4 layer it needs.**  Every conjunct of `Case2Numeric2`
follows once the §4 (7)/(8) object layer is available:

* `hSeven` — Bender §4 (7) (the design's `Case2SevenFacts`; kept for bookkeeping);
* `hEight` — Bender §4 (8) for every prime-order `P ≤ F` (`Case2EightAll`): it produces `p`, `P`,
  the `(p,p)`-subgroup `A ≤ F ⊔ K`, `p ∣ |K₀|`, `N_U(P) = U ⊓ M ≤ N(A)`, odd `p₀ ≤ p₁ ≤ p+1`,
  `p₀ ≤ p`, and (unless `Case2InvNormal`) `u ≤ p` and `3 ≤ p₀`;
* `hpar` — §4 (10) with the *canonical* order `q = qOf h` of §4 (9): now **proved** as
  `Work.CORE4.Case2ParityQOf` (`Submission.Work.CORE4.Case2ParityQOf`, imported here), so this
  assembly no longer takes it as a hypothesis;
* `hK` — §4 (9): `k = |K| · |S₀|`;
* `hInv` — the exclusion of Bender's exceptional case of (8);
* `hB0S` — §4 (2) in the form `B₀ ≤ C_U(S)`;
* `hCount` — Bender's (11): `P·E` contains `(p₁ − 1) q k'` conjugates `X ≠ P` of `P`.

With these, the only remaining content is arithmetic and index bookkeeping, done here. -/
theorem Case2Numeric2_of_layer (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (hSeven : Work.GW2.Case2SevenFacts B h.D)
    (hEight : Work.GW2.Case2EightAll B h.D)
    (hK : ∀ q k k' : ℕ, Odd q → 7 ≤ q →
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) →
      (h.D.M ⊓ B.H).relIndex h.D.M = q * k' → k = Nat.card ↥h.D.K * Nat.card ↥B.S0)
    (hInv : ¬ Work.GW2.Case2InvNormal B h.D)
    (hB0S : h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G))
    (hCount : ∀ (q k k' p : ℕ) (P A : Subgroup G) (p1 : ℕ),
      Odd q → 7 ≤ q → Even k → Odd k' →
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) →
      (h.D.M ⊓ B.H).relIndex h.D.M = q * k' →
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 → p ∣ Nat.card ↥h.D.K →
      p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
      A ≤ h.D.F ⊔ h.D.K → Nat.card ↥A = p ^ 2 → (∀ x ∈ A, x ^ p = 1) → P ≤ A →
      (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
          (∀ x ∈ B', x ^ p = 1) → B' = A) →
      p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard →
      {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
          ∃ g : G, X = Work.GW2.conjSub g P}.ncard = (p1 - 1) * q * k' + 1) :
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
      {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
          ∃ g : G, X = Work.GW2.conjSub g P}.ncard = (p1 - 1) * q * k' + 1 ∧
      3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  classical
  -- §4 (10) with the canonical field order (`Case2ParityQOf`, proved).
  obtain ⟨k, k', hqodd, hq7, hkeven, hk'odd, hcases, hrelMH⟩ :=
    Work.CORE4.Case2ParityQOf G I hbc B h
  -- §4 (8): `p := |F|.minFac` and `P ≤ F` of order `p` (Cauchy in the finite group `F`).
  obtain ⟨hpprime, -, P, hPF, hPcard⟩ := Work.CORE4.Case2Fill G B h
  -- §4 (8): Bender's objects for this `p` and `P`.
  obtain ⟨A, hObj, hFacts⟩ := hEight (Nat.card ↥h.D.F).minFac P hpprime hPF hPcard
  obtain ⟨hpprime', hPF', hPcard', hAle0, hAcard, hAexp, hPAsub, hAuniq⟩ := hObj
  obtain ⟨hpK0, -, hNP, hNPA, hp0odd, hp0p1, hp1p, hp0p, -, hdisj⟩ := hFacts
  -- `p ∣ |K|`: `p ∣ |K₀| ≤ |K|`.
  have hpK : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.K :=
    dvd_trans hpK0 (Subgroup.card_dvd_of_le inf_le_right)
  -- `A ≤ F ⊔ K` is Bender's §4 (8) object data (conjunct of `Case2EightObj`).
  -- §4 (9): `k = |K| · |S₀|`.
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 := hK (qOf h) k k' hqodd hq7 hcases hrelMH
  -- The exceptional case of (8) is excluded, so `u ≤ p` and (with `U ⊄ M`) `3 ≤ p₀`.
  have hup : Work.GW2.Case2EightU B A ≤ (Nat.card ↥h.D.F).minFac := by
    rcases hdisj with hcase | hcase
    · exact absurd hcase hInv
    · exact hcase.1
  have hp03 : 3 ≤ Work.GW2.Case2EightP0 B P A := by
    rcases hdisj with hcase | hcase
    · exact absurd hcase hInv
    · exact hcase.2.2 (Case2N2_not_U_le_M I B h)
  refine ⟨qOf h, k, k', (Nat.card ↥h.D.F).minFac, P, A, Work.GW2.Case2EightU B A,
    Work.GW2.Case2EightP0 B P A, Work.GW2.Case2EightP1 P A, rfl, hqodd, hq7, hkeven, hk'odd,
    hcases, hrelMH, hkK, hpK, hpprime', hPF', hPcard', hAle0, hAcard, hAexp, hPAsub, hAuniq,
    rfl, rfl, rfl, ?_, hB0S, ?_, hp03, hp0odd, hp0p1, hp1p, hp0p,
    Case2N2_two_p_le_k B h hkK hpK, Case2N2_one_le_u B A, hup⟩
  · -- §4 (10): `|H : H ⊓ M| = u · p₀`.
    simpa only [Work.GW2.Case2EightU, Work.GW2.Case2EightP0] using
      Case2N2_MH_relIndex I B h hNP hNPA
  · -- Bender's (11), from the hypothesis `hCount`.
    exact hCount (qOf h) k k' (Nat.card ↥h.D.F).minFac P A (Work.GW2.Case2EightP1 P A)
      hqodd hq7 hkeven hk'odd hcases hrelMH hkK hpK hpprime' hPF' hPcard' hAle0 hAcard
      hAexp hPAsub hAuniq rfl

/-- Bender 1981, §4 (7)–(11) and the objects of p. 225: the numbers `q, k, k', p`, the
subgroups `P ≤ F` (of order `p`) and `A ≤ F·K` (the unique subgroup of type `(p,p)`, containing
`P`), the numbers `u = |U : N_U(A)|`, `p₀ = |N_U(A) : N_U(P)|`, `p₁ = #{conjugates of P in A}`,
all the inequalities Bender derives in (8) (`3 ≤ p₀`, `p₀` odd, `p₀ ≤ p₁ ≤ p+1`, `p₀ ≤ p`,
`2p ≤ k`, `1 ≤ u ≤ p`), the parity data of §4 (10) with `q = qOf h` (§4 (9)), the identities
`k = |K|·|S₀|`, `p ∣ |K|`, `|H : H ⊓ M| = u·p₀`, §4 (5) in the form `B₀ ≤ C_U(S)`, and Bender's
(11): `P·E` contains `(p₁ − 1) q k'` conjugates `X ≠ P` of `P` (counted as `ncard = (p₁−1)qk' + 1`
including `P` itself). -/
theorem Case2Numeric2 :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          q = Work.CORE4.qOf h ∧ Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
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
          {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
              ∃ g : G, X = Work.GW2.conjSub g P}.ncard = (p1 - 1) * q * k' + 1 ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  sorry

end Work.CORE4

