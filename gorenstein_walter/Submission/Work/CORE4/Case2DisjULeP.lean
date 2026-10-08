/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender §4 (8): `u ≤ p` at the `Case2Ctx` level

The requested statement is Bender 1981, §4 (8), p. 226: *unless* `I_U(s) ⊴ Ĥ` one has
`u := |U : N_U(A)| ≤ p`, where `P ≤ F = C_{F(U)}(s)` has prime order `p` and `A` is the
`(p,p)`-subgroup of `F ⊔ K` containing `P` (here `Work.GW2.Case2EightObj h.D p P A`).

    theorem Case2DisjULeP (I : C4Inputs) : BenderCtx G → ∀ B (h : Case2Ctx B),
      ¬ Case2InvNormal B h.D → ∀ p P A, p.Prime → P ≤ h.D.F → Nat.card P = p →
        Case2EightObj h.D p P A → Case2EightU B A ≤ p

## Verdict: not derivable from this hypothesis list (missing hypothesis)

The statement is mathematically true in Bender's configuration, but the recorded hypotheses do not
carry the input his proof consumes, and nothing in the workspace supplies it.  This file therefore
keeps the requested statement untouched (`sorry`) and proves the two exact reductions below, which
isolate the missing input.  Everything else in the file is a real proof.

**1. What the hypotheses do give.**  `A ≤ U ⊓ M` (`A ≤ F ⊔ K`, `F ≤ U ⊓ M`, `K ≤ U ⊓ M`),
`U ⊓ M ≤ N_G(A)` (`Case2Eight_le_normalizer_A`, from `F ⊴ M` and `K ⊴ U ⊓ M`), and
`N_U(P) = U ⊓ M` (`Case2Eight_NU`).  Hence Bender's (11) holds as an identity, *proved below*
(`case2EightU_mul_P0_c4`):

    u * p₀ = |U : U ⊓ M| ,      p₀ = Case2EightP0 B P A = |N_U(A) : N_U(P)| = |N_U(A) : U ⊓ M| .

Consequently (`case2EightU_le_p_iff_c4`) the conclusion `u ≤ p` is *equivalent* to the bound
`|U : U ⊓ M| ≤ p * p₀`: the recorded data constrain the product `u * p₀`, never `u` or `p₀`
separately, and give no upper bound for `|U : U ⊓ M|`.

**2. What Bender's proof of (8) uses, and why it is missing.**  Bender puts
`Q := Ω₁(Z₂(O_p(U)))` — the second centre of the `p`-core, the subgroup `Qsub p B` — and asserts,
*without proof*,

    either `A = Q`, or `Z(Q) < A < Q` and `|Q : A| = p`, or `s` inverts `Q`.

The first two branches give `u ≤ p`: `A = Q` is characteristic in `U` (so `u = 1`), and in the
middle branch the `U`-conjugates of `A` lie among the `p + 1` subgroups of `Q` of order `p²`
containing the `U`-invariant `Z(Q)`, while `u` is odd.  That counting is *formalised and proved*
in this workspace as `Work.CORE4.eightU_le_p_of_case2` (`CORE4/EightULeP.lean`), and the third
branch is the hypothesis `¬ Case2InvNormal B h.D`, which is in fact a *theorem* of the remaining
hypotheses (`Work.CORE4.not_Case2InvNormal_of_ctx`, `CORE4/S0CentUO2.lean`).  Hence the only open
input is the *position of `A` inside `Q`*,

    hAQ  : A ≤ Qsub p B     and     hPos : A = Qsub p B ∨ (Z(Qsub) < A ∧ A.relIndex Qsub = p) ,

and with it the requested statement follows verbatim — this is the proved theorem
`Case2DisjULeP_of_Qpos` below.

The recorded hypotheses never mention `Ω₁(Z₂(O_p(U)))` and bound neither its order nor the position
of `A` inside it: `Case2EightObj` constrains `A` only inside the *abelian* `F ⊔ K`
(`A = Ω₁(F ⊔ K)`, unique), and `Case2Ctx` records §4 (1)–(9) — `U ⊓ M = K ⊔ B₀` with
`K = I_{U⊓M}(s)` cyclic, `F(U) ⊓ M = K₀ ⊔ F` with `F = B₀ ⊓ F(U)` cyclic `≠ 1`, `N_G(F) = M`,
`F ⊓ F^g = 1` for `g ∉ M`, and `E(M) ≅ L₂(q)` with `S ≤ E(M)` — none of which bounds the exponent
or the second centre of `O_p(U)`.

**3. Why the missing input is not derivable.**  Conjunct 1 (`A ≤ Qsub p B`) is *implied by*
`A ⊴ O_p(U)`: if `A ⊴ O_p(U)` then `A` is a normal elementary abelian subgroup of order `p²` of
the `p`-group `O_p(U)`, so `A ≤ Z₂(O_p(U))` (the proved `Work.CORE4.E2Z2le`), whence
`A ≤ Ω₁(Z₂(O_p(U))) = Qsub p B` (as `A` has exponent `p`).  So the missing input is at least as
strong as Bender's object-layer input `Work.CORE4.APcoreCtx` (`A ⊴ O_p(U)`, unproved), and every
route to it in the tree (`EightAnormalPcore`, `EightAnormalPcore_of_Qpos`, `EightANF_QsubPos`)
takes `Work.CORE4.EightQsubA` — i.e. this very position datum — as its only input, so the
available argument is circular; and the hypotheses never mention `Ω₁(Z₂(O_p(U)))`.

Conjuncts 2–3 are moreover refuted by the local configuration recorded in
`CORE4/EightTrichOfCtx.lean` (`p` odd, `U ≅ C_p³` with the involution `σ = diag(1,-1,-1)`,
`U ⊓ M = ⟨v₁,v₂⟩`, `B₀ = C_U(σ) = F = ⟨v₁⟩`, `K = I_{U⊓M}(σ) = ⟨v₂⟩`, `A = Ω₁(F ⊔ K₀) = ⟨v₁,v₂⟩`,
`Q := Qsub p B = U`): there `A ≤ Q` holds but `A ≠ Q` and `Z(Q) = Q = C_p³ ≰ A`, so both open
alternatives of the trichotomy fail although everything the hypotheses assert about this local
structure holds.

**4. Independent verdicts.**  The sub-lemma `Submission/Work/CORE4Disj/Qrel.lean` — requested from
this file, with exactly the position data `hAQ`, `hPos` of §2 as its conclusion — came back
`declare_false` ("mis-stated / missing a structural hypothesis; conjunct 1 is `A ⊴ O_p(U)`, and
conjuncts 2–3 are refuted by the `U ≅ C_p³` model").  The two *reviews* of the two sub-lemma
statements requested from this file (`A ≤ Qsub ∧ Z(Qsub) ≤ A`, resp. that plus
`A.relIndex Qsub = p`) both returned "probably wrong as stated: `centerIn (Qsub p B) ≤ A` is not
implied by `Case2EightObj` alone".  The same statement stands (unproved) as
`Work.CORE4.EightULeP`, `Work.CORE4.CtxDisjULeP` and `Work.CORE4.Case2EightUAnormalCtx`; the
provers of `CtxDisjULeP`, of the trichotomy (`CORE4/EightTrichOfCtx.lean`,
`CORE4/CtxTrichOfCtx2.lean`: "under-hypothesised — declare_false") and of the case-3 leaves
(`CORE4/EightExCase3.lean`, `CORE4/Case2EightCase3U9.lean`) recorded the same verdict; and the
area's own `Case2Ctx`-level assembly of the second branch of (8) (`CORE4/Case2EightCasesOfCtx.lean`)
carries its single remaining `sorry` at precisely this step `hpos`.

**5. The repair.**  Add `hAQ` and `hPos` of §2 as hypotheses; then `Case2DisjULeP_of_Qpos`
(proved below) gives the conclusion.  (The remaining conjuncts of the counting lemma,
`U ≤ N_G(Qsub)` and the exponent of `Qsub`, are proved here as `U_le_normalizer_Qsub_c4` and
`Qsub_pow_eq_one_c4`.)
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.Case2EightAllOfCtx
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.EightULeP
import Submission.Work.CORE4.Case2EightQfacts

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Bender's (11): `u * p₀ = |U : U ⊓ M|` -/

/-- `A ≤ U ⊓ M`: `A ≤ F ⊔ K` with `F ≤ U ⊓ M` and `K ≤ U ⊓ M`. -/
theorem A_le_UinfM_c4_ulep {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) {p : ℕ}
    {P A : Subgroup G} (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ B.U ⊓ h.D.M :=
  hObj.2.2.2.1.trans
    (sup_le (Work.GW2.Case2Data.F_le_UinfM B h.D) (Work.GW2.Case2Data.K_le B h.D))

/-- **Bender's (11)** (p. 225), for the `§4` configuration: with `u = |U : N_U(A)|` and
`p₀ = |N_U(A) : N_U(P)| = |N_U(A) : U ⊓ M|`, the product is the index of `U ⊓ M` in `U`. -/
theorem case2EightU_mul_P0_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    Work.GW2.Case2EightU B A * Work.GW2.Case2EightP0 B P A = (B.U ⊓ h.D.M).relIndex B.U := by
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  let h6 : Work.GW2.Case2Ctx6 B := Work.CORE4.ctx6_of_ctx h
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M :=
    Case2Eight_NU B h6 P hPF hpne
  have hMN : B.U ⊓ h.D.M ≤ Subgroup.normalizer (A : Set G) :=
    Case2Eight_le_normalizer_A I B h6 p P A hObj
  have hKP : B.U ⊓ h.D.M ≤ B.U ⊓ Subgroup.normalizer (A : Set G) := le_inf inf_le_left hMN
  have hp0eq : Work.GW2.Case2EightP0 B P A =
      (B.U ⊓ h.D.M).relIndex (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [Work.GW2.Case2EightP0, hNU]
  rw [Work.GW2.Case2EightU, hp0eq, mul_comm]
  exact Subgroup.relIndex_mul_relIndex (H := B.U ⊓ h.D.M)
    (K := B.U ⊓ Subgroup.normalizer (A : Set G)) (L := B.U) hKP inf_le_left

/-- Consequence of Bender's (11): `u` divides `|U : U ⊓ M|`, the only upper bound on `u` that the
recorded hypotheses provide. -/
theorem case2EightU_dvd_relIndex_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    Work.GW2.Case2EightU B A ∣ (B.U ⊓ h.D.M).relIndex B.U :=
  ⟨_, (case2EightU_mul_P0_c4 I B h p P A hp hPF hPcard hObj).symm⟩

/-- `p₀ = Case2EightP0 B P A ≠ 0` (a relative index in a finite group). -/
theorem case2EightP0_pos_c4 (B : Work.GW2.BenderSetup G) (P A : Subgroup G) :
    0 < Work.GW2.Case2EightP0 B P A := by
  rw [Work.GW2.Case2EightP0]
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hcard := Subgroup.relIndex_mul_card
    (B.U ⊓ Subgroup.normalizer (P : Set G)) (B.U ⊓ Subgroup.normalizer (A : Set G))
  rw [h0, zero_mul] at hcard
  exact Nat.card_pos.ne' hcard.symm

/-- **The exact shape of the gap.**  Bender's (11) makes `u ≤ p` *equivalent* to
`|U : U ⊓ M| ≤ p * p₀`. -/
theorem case2EightU_le_p_iff_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    Work.GW2.Case2EightU B A ≤ p ↔
      (B.U ⊓ h.D.M).relIndex B.U ≤ p * Work.GW2.Case2EightP0 B P A := by
  have hmul := case2EightU_mul_P0_c4 I B h p P A hp hPF hPcard hObj
  have hpos : 0 < Work.GW2.Case2EightP0 B P A := case2EightP0_pos_c4 B P A
  constructor
  · intro hu
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hu
  · intro hb
    have hb' : Work.GW2.Case2EightU B A * Work.GW2.Case2EightP0 B P A ≤
        p * Work.GW2.Case2EightP0 B P A := by rw [hmul]; exact hb
    exact Nat.le_of_mul_le_mul_right hb' hpos

/-! ## 2. The two `Qsub`-facts that are available

`Q` is normalised by `U` (`CORE4/QsubNormal.lean`, unconditional) and has exponent `p` for odd `p`
(the route of `Case2EightQfacts`, via `Qsub_eq_map_omega1UpperCentralTwo`). -/

/-- `U ≤ N_G(Qsub p B)`: `Qsub p B = Ω₁(Z₂(O_p(U)))` is characteristic in `O_p(U) ⊴ U`. -/
theorem U_le_normalizer_Qsub_c4 (p : ℕ) (B : Work.GW2.BenderSetup G) :
    B.U ≤ Subgroup.normalizer ((Qsub p B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show Work.GW2.conjSub g (Qsub p B) = Qsub p B
  have hP : Work.GW2.conjSub g (Work.GW2.pCoreIn p B.U) = Work.GW2.pCoreIn p B.U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (pCoreIn_le_normalizer p B.U hg)
  calc Work.GW2.conjSub g (Qsub p B)
      = Work.GW2.conjSub g (omega1 p (z2 (Work.GW2.pCoreIn p B.U))) := rfl
    _ = omega1 p (Work.GW2.conjSub g (z2 (Work.GW2.pCoreIn p B.U))) := conjSub_omega1 g p _
    _ = omega1 p (z2 (Work.GW2.conjSub g (Work.GW2.pCoreIn p B.U))) := by rw [conjSub_z2]
    _ = omega1 p (z2 (Work.GW2.pCoreIn p B.U)) := by rw [hP]
    _ = Qsub p B := rfl

/-- `Qsub p B` has exponent `p` (`p` odd), Bender 1.9(i). -/
theorem Qsub_pow_eq_one_c4 (p : ℕ) (B : Work.GW2.BenderSetup G) (hpodd : Odd p) :
    ∀ x ∈ Qsub p B, x ^ p = 1 := by
  intro x hx
  rw [Qsub_eq_map_omega1UpperCentralTwo p B] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hy' := OddOrder.GroupTheory.pow_eq_one_of_mem_omega1UpperCentralTwo hpodd hy
  rw [← map_pow, hy', map_one]

/-! ## 3. The statement from the missing input

The `Q`-position of `A` (Bender's cases 1–2) plus the two `Qsub`-facts already available in the
workspace (`U ≤ N_G(Qsub)`, exponent `p`) give the requested statement: case 1 makes `u = 1`
(`A = Qsub` is characteristic in `U`), and case 2 is exactly the counting lemma
`eightU_le_p_of_case2` proved in `CORE4/EightULeP.lean`. -/

/-- **The requested statement from the `Q`-position of `A`.**  This is the precise missing input:
with `hQN : U ≤ N_G(Qsub)`, `hQexp` (exponent `p` on `Qsub`), `hAQ : A ≤ Qsub` and
`hPos : A = Qsub ∨ (Z(Qsub) < A ∧ A.relIndex Qsub = p)`, the conclusion `u ≤ p` follows. -/
theorem Case2DisjULeP_of_Qpos (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hQN : B.U ≤ Subgroup.normalizer ((Qsub p B : Subgroup G) : Set G))
    (hQexp : ∀ x ∈ Qsub p B, x ^ p = 1)
    (hAQ : A ≤ Qsub p B)
    (hPos : A = Qsub p B ∨
      (centerIn (Qsub p B) < A ∧ A.relIndex (Qsub p B) = p)) :
    Work.GW2.Case2EightU B A ≤ p := by
  rcases hPos with hAeq | ⟨hZlt, hidx⟩
  · -- case 1: `A = Qsub` is characteristic in `U`, so `N_U(A) = U` and `u = 1`
    have hUleN : B.U ≤ Subgroup.normalizer (A : Set G) := by rw [hAeq]; exact hQN
    have hu : Work.GW2.Case2EightU B A = 1 := by
      rw [Work.GW2.Case2EightU, inf_eq_left.mpr hUleN, Subgroup.relIndex_self]
    rw [hu]
    exact hp.one_le
  · -- case 2: the orbit count, `Work.CORE4.eightU_le_p_of_case2`
    have hpodd : Odd p := by
      have h1 : p ∣ Nat.card ↥h.D.F := by
        rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
      have h2 : Nat.card ↥h.D.F ∣ Nat.card ↥B.U :=
        Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_U B h.D)
      exact Odd.of_dvd_nat B.U_odd (h1.trans h2)
    exact eightU_le_p_of_case2 B hp hpodd hQN hAQ hZlt hObj.2.2.2.2.1 hidx hQexp

/-! ## 4. The requested statement

Left exactly as the area's file gave it: the position data `hAQ`, `hPos` of
`Case2DisjULeP_of_Qpos` above is not a consequence of these hypotheses (see the header). -/

theorem Case2DisjULeP (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          Work.GW2.Case2EightU B A ≤ p := by sorry

end Work.CORE4
