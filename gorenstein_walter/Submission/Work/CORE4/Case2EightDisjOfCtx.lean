/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# CORE4 — Bender §4 (8) at the `Case2Ctx` level

The statement (Bender 1981, §4 (8), pp. 225–226 = the last conjunct of `Case2EightFacts`):

    Case2InvNormal B D ∨ (u ≤ p ∧ A ⊴ F(U) ∧ (U ⊄ M → 3 ≤ p₀))

where `u = |U : N_U(A)|`, `p₀ = |N_U(A) : N_U(P)|` and `A` is the `(p,p)`-subgroup of `F ⊔ K`
containing `P ≤ F` of prime order `p`.

## STATUS (verdict of the prover of this file)

**Under-hypothesised: not derivable from the listed hypotheses.**  The first disjunct is *refuted*:
`Work.CORE4.not_Case2InvNormal_of_ctx` (`CORE4/S0CentUO2.lean`, sorry-free) proves
`¬ Case2InvNormal B h.D` from `BenderCtx G` + `Case2Ctx B` alone (via `[S₀,U] = ⊥` and Bender's
Lemma 2.8).  So the statement is here *equivalent* to its second half.  Of its three conjuncts, two
are proved below — `3 ≤ p₀` in this file, and `A ⊴ F(U)` reduces (per an independent prover) to the
area's unproved object-layer leaf `Work.CORE4.APcoreCtx`, i.e. `A ⊴ O_p(U)` — while the third,
`u ≤ p`, is Bender's §4 (8) dichotomy, which is not a consequence of the recorded data.

The delegated leaf `Work.CORE4.Case2DisjULeP` (this file's child) returned it as not derivable while
*proving* the reductions `case2EightU_mul_P0_c4` (Bender's (11) identity `u · p₀ = |U : U ⊓ M|`) and
`Case2DisjULeP_of_Qpos`: `u ≤ p` follows from the *position of `A` inside `Q := Ω₁(Z₂(O_p(U)))`*
(`A ≤ Q` and `A = Q ∨ (Z(Q) < A ∧ A.relIndex Q = p)`) together with the already-proved counting
step `eightU_le_p_of_case2`, and that position datum is not derivable — `A ≤ Q` would follow from
`A ⊴ O_p(U)` (via the proved `E2Z2le`), but every route to `A ⊴ O_p(U)` in the area's tree takes
that same datum as input, and the middle alternatives of the trichotomy are refuted by the local
configuration `U ≅ C_p³`, `σ = diag(1,-1,-1)`, `U ⊓ M = ⟨v₁,v₂⟩`, `B₀ = F = ⟨v₁⟩`, `K = ⟨v₂⟩`,
`A = ⟨v₁,v₂⟩`, `Q = U` (there `A ≤ Q`, `A ≠ Q`, `Z(Q) = Q ≰ A`).  Equivalently, `u ≤ p` is implied
by Bender's index bound `|U : B₀ K F(U)| ≤ p`, which `CORE4/Case2EightIndexOfCtx.lean` (the area's
own file) records as *not a formal consequence of the (1)–(6) data*, its intended proof needing the
trichotomy leaf `Case2EightTrich9`, itself reported not derivable.

The statement becomes provable with that input added, e.g. as a hypothesis
`h : (h.D.B0 ⊔ h.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ p`; then `A ⊴ F(U)` (child leaf)
gives `N_U(A) ⊇ (U ⊓ M) · F(U)` and hence `u ≤ h`, and everything else is proved here.

## Structure of the proof

The branch that matters is `¬ Case2InvNormal B h.D` (the other one is the left disjunct).  There
the two *deep* inputs are Bender's §4 (8) analysis for the first two cases of the trichotomy on
`Q = Ω₁(Z₂(O_p(U)))`:

* `Work.CORE4.Case2DisjULeP`    — `u ≤ p`,
* `Work.CORE4.Case2DisjANormal` — `A ⊴ F(U)`.

Both are delegated leaves stated at exactly this level (with `¬ Case2InvNormal` as a hypothesis);
in the workspace they are the two open inputs of the `(8)` layer (`EightULeP.lean`,
`EightANormalFitting.lean`).

Everything else is proved *here*:

* Bender's (3) (`SixThree`): `F(U) ⊓ M = K₀ ⊔ F`;
* `EightAeqOmega`: `A = Ω₁(F ⊔ K₀)`;
* the third conjunct `3 ≤ p₀`, by the elementary case analysis on `F(U) ≤ M`:

  - if `F(U) ≤ M`, then `F(U) = K₀ ⊔ F` and `A = Ω₁(F(U))`, which is normalized by `U`
    (`Ω₁` commutes with conjugation); hence `p₀ = |U : U ⊓ M|`, which is odd and `> 1` because
    `U ⊄ M` (`H = U ⊔ S` and `S ≤ M`);
  - otherwise `p₀ = |N_U(A) : U ⊓ M| ≥ |(U ⊓ M)(F(U)) : U ⊓ M| = |F(U) : F(U) ⊓ M| > 1`
    (using `A ⊴ F(U)`), and `p₀` is odd.

Note that `N_U(P) = U ⊓ M` (`Case2Eight_NU`, since `P ≤ F` has prime order and `N_G(F) = M`),
which is what identifies `p₀` with `|N_U(A) : U ⊓ M|`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2EightAllOfCtx

namespace Work.CORE4

open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## Conjugation commutes with `Ω₁` -/


/-- Forget the §4 (7)–(9) part of a `Case2Ctx`. -/
def ctx6OfCtx_c4 {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    Work.GW2.Case2Ctx6 B :=
  ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩

/-! ## `A ≤ F(U)` and `A = Ω₁(F(U))` when `F(U) ≤ M` -/

/-- `A = Ω₁(F ⊔ K₀)` (`EightAeqOmega`), hence `A ≤ F(U)`. -/
theorem A_le_fittingIn_c4 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.fittingIn B.U := by
  obtain ⟨-, hAeq⟩ := EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj
  rw [hAeq]
  refine le_trans ((Subgroup.closure_le (h.D.F ⊔ Work.GW2.Case2Data.K0 h.D)).mpr ?_) ?_
  · intro x hx; exact hx.1
  · exact sup_le (Work.GW2.Case2Data.F_le_fitting B h.D) inf_le_left


/-! ## The third conjunct `3 ≤ p₀` -/

theorem three_le_p0_of_not_invNormal (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (_hInv : ¬ Work.GW2.Case2InvNormal B h.D)
    (hAn : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal) :
    3 ≤ Work.GW2.Case2EightP0 B P A := by
  -- elementary §4 (8) reductions
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M :=
    Case2Eight_NU B (ctx6OfCtx_c4 h) P hPF hpne
  have hMN : B.U ⊓ h.D.M ≤ Subgroup.normalizer (A : Set G) :=
    Case2Eight_le_normalizer_A I B (ctx6OfCtx_c4 h) p P A hObj
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact hMN
  have hp0odd : Odd (Work.GW2.Case2EightP0 B P A) := Case2Eight_odd_p0 B p P A h4
  have hp0eq : Work.GW2.Case2EightP0 B P A =
      (B.U ⊓ h.D.M).relIndex (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [Work.GW2.Case2EightP0, hNU]
  have relIndex_pos : ∀ H K : Subgroup G, 0 < H.relIndex K := by
    intro H K
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hcard := Subgroup.relIndex_mul_card H K
    rw [h0, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  have hunotM : ¬ B.U ≤ h.D.M := by
    intro hUM
    exact Work.GW2.Case2Pre.not_H_le B h.D h.pre
      ((Work.GW2.Case2Ctx.H_eq_U_sup_S I h).trans_le (sup_le hUM h.S_le_M))
  by_cases hFM : Work.GW2.fittingIn B.U ≤ h.D.M
  · -- ### Case (a): `F(U) ≤ M`
    have hAeq : A = omega1 p (Work.GW2.fittingIn B.U) :=
      A_eq_omega1_fittingIn_of_le_M I hbc B h p P A hp hPF hPcard hObj hFM
    have hUleN : B.U ≤ Subgroup.normalizer (A : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hAeq]
      exact conjSub_omega1_fittingIn_eq B p hu
    have hp0eq' : Work.GW2.Case2EightP0 B P A = (B.U ⊓ h.D.M).relIndex B.U := by
      rw [hp0eq, inf_eq_left.mpr hUleN]
    rw [hp0eq']
    have hne1 : (B.U ⊓ h.D.M).relIndex B.U ≠ 1 := by
      intro h1
      have hUle : B.U ≤ B.U ⊓ h.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ h.D.M) (K := B.U)).mp h1
      exact hunotM (le_trans hUle inf_le_right)
    have hpos : 0 < (B.U ⊓ h.D.M).relIndex B.U := relIndex_pos _ _
    have hgt1 : 1 < (B.U ⊓ h.D.M).relIndex B.U := by omega
    have hodd : Odd ((B.U ⊓ h.D.M).relIndex B.U) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.relIndex_dvd_card (B.U ⊓ h.D.M) B.U)
    obtain ⟨k, hk⟩ := hodd
    omega
  · -- ### Case (b): `F(U) ⊄ M`
    have hAleFU : A ≤ Work.GW2.fittingIn B.U :=
      A_le_fittingIn_c4 I hbc B h p P A hp hPF hPcard hObj
    have hFUleN : Work.GW2.fittingIn B.U ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAleFU).mp hAn
    have hsup : (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U ≤
        B.U ⊓ Subgroup.normalizer (A : Set G) :=
      sup_le (le_inf inf_le_left hMN) (le_inf (Subgroup.map_subtype_le _) hFUleN)
    have htower := Subgroup.relIndex_mul_relIndex (H := B.U ⊓ h.D.M)
      (K := (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U)
      (L := B.U ⊓ Subgroup.normalizer (A : Set G)) le_sup_left hsup
    have hle : (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) ≤
        Work.GW2.Case2EightP0 B P A := by
      rw [hp0eq, ← htower]
      exact Nat.le_mul_of_pos_right _ (relIndex_pos _ _)
    have hne1 : (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) ≠ 1 := by
      intro h1
      have hle' : (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U ≤ B.U ⊓ h.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ h.D.M)
          (K := (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U)).mp h1
      exact hFM (le_trans (le_trans le_sup_right hle') inf_le_right)
    have hpos : 0 < (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) :=
      relIndex_pos _ _
    have hgt1' : 1 < (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) := by
      omega
    have hgt1 : 1 < Work.GW2.Case2EightP0 B P A := lt_of_lt_of_le hgt1' hle
    obtain ⟨k, hk⟩ := hp0odd
    omega

/-! ## The target -/


end Work.CORE4
