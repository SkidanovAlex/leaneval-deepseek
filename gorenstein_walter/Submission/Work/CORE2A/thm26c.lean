/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE2A.bender26c_stepA
import Submission.Work.CORE2A.bender26c_stepE
import Submission.Work.CORE2A.bender26c_stepW1_case
import Submission.Work.CORE2A.stepS1_bender
import Submission.Work.ASM.Basic
import Submission.Work.BMAX.Bender17i_dedekind_basic

/-!
# CORE2A: Bender 1981, Theorem 2.6, step 3 (`Thm26cProp`)

Bender 1981, p. 220 (proof of Theorem 2.6): after `O₂(Ĥ) ≠ 1` and `E(Ĥ) ≠ 1` have been
disposed of,

> "it suffices to show that `t` centralizes every `H`-invariant `p`-subgroup `P` of `G`, `p` an
> odd prime.  Suppose `[t,P] ≠ 1`.  Choose `P` minimal and `Ĥ ⊇ N_G(P)`."

This is `Work.GW2.Thm26cProp`.

## Structure of the proof (as formalised here)

`thm26c_of_stepE` is the assembly: it reduces `Thm26cProp` to the **single** configuration
statement `stepE` of Bender's p. 221 paragraph.  Given a minimal counterexample `P`:

* `N_G(P) ≠ ⊤` (simplicity), so a coatom `M ⊇ N_G(P)` exists; `M` is a proper subgroup, hence a
  D-group, and `B' := {B with Hhat := M}` is a Bender setup, so `h21` gives
  `¬ OneInvClassIn M`;
* `bender26c_stepA` (Bender's Lemma 2.1 + 1.1(iii) + orbit–stabiliser) produces a four-group
  `V ≤ S`, an element `s ∈ V#` and `g ∈ N_G(V) \ M` with `g t g⁻¹ = s` and
  `C_P(s) ≰ C_P(t)`;
* `bender26c_stepP1` (proved) gives `P₁ := ⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ O_p(M^g)`, while
  `b26c_commutator_eq`/`b26c_commutator_le_pCoreIn` give `P = ⁅⟨t⟩,P⁆ ≤ O_p(M)`, hence
  `P₁ ≤ P ≤ F(M)`;
* `stepE` then supplies `N_G(P₁) ⊓ F*(M) ≤ M^g`, i.e. `BRel M (conjSub g M)` with witness `P₁`;
* since `P₁ ≤ O_p(M) ≠ ⊥` we get `O(M) ≠ ⊥`, so Lemma 2.5 (`h25`) applies to `B'` and gives
  `M^g = M`, whence `g ∈ M` — contradicting `g ∉ M`.

Everything but `stepE` is proved here.  `stepE` is Bender's assertion "`P₁` centralizes `P^g`"
together with Lemmas 2.3/2.4 applied to a maximal `M' ⊇ N_G(P₁)` and to `M^g`; it is the
mathematical content of Bender's pp. 220–221 for this step.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. Elementary API -/

/-- `conjSub g K = K` means that `g` normalizes `K`. -/
theorem mem_normalizer_of_conjSub_eq {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (h : conjSub g K = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ K ↔ g * x * g⁻¹ ∈ K := by
    have h2 : (g * x * g⁻¹) ∈ conjSub g K ↔ (g * x * g⁻¹) ∈ K := by rw [h]
    rwa [mem_conjSub_iff] at h2
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  exact h1

/-- Strictly smaller subgroups have strictly smaller cardinality. -/
theorem card_lt_card_of_lt {G : Type*} [Group G] [Finite G] {Q P : Subgroup G} (h : Q < P) :
    Nat.card Q < Nat.card P := by
  have hle : Nat.card Q ≤ Nat.card P :=
    Nat.card_le_card_of_injective
      (f := fun x : Q => (⟨x.1, h.1 x.2⟩ : P))
      (fun a b hab => Subtype.ext (congrArg (fun y : P => (y : G)) hab))
  rcases lt_or_eq_of_le hle with h' | h'
  · exact h'
  · exfalso
    have hQP : Q = P := Subgroup.eq_of_le_of_card_ge h.1 (le_of_eq h'.symm)
    exact h.2 (by rw [← hQP])

/-- If `t ∈ M` and `M` does not have a single class of involutions, then some involution of `M`
is not `M`-conjugate to `t`. -/
theorem exists_involution_not_conj_t {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (ht : B.t ∈ M)
    (h2 : ¬ Work.GW2.OneInvClassIn M) :
    ∃ x ∈ M, orderOf x = 2 ∧ ∀ m ∈ M, m * B.t * m⁻¹ ≠ x := by
  classical
  by_contra hcon
  push Not at hcon
  refine h2 ?_
  intro x hx y hy
  obtain ⟨hxM, hx2⟩ := hx
  obtain ⟨hyM, hy2⟩ := hy
  obtain ⟨m₁, hm₁M, hm₁⟩ := hcon x hxM hx2
  obtain ⟨m₂, hm₂M, hm₂⟩ := hcon y hyM hy2
  refine ⟨m₂ * m₁⁻¹, M.mul_mem hm₂M (M.inv_mem hm₁M), ?_⟩
  rw [← hm₁, ← hm₂]
  group

/-- The join of the normal `p`-subgroups of a group is a `p`-group (local copy). -/
theorem thm26c_isPGroup_sSup_normal_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(sSup {N : Subgroup L | N.Normal ∧ IsPGroup p N}) :=
  Sylow.sSup_of_normal _ (fun _ hN => hN.2) (fun _ hN => hN.1)

/-- `O_p(L)` is a `p`-group (local copy). -/
theorem thm26c_pCore_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(Work.GW2.pCore p L) := by
  rw [Work.GW2.pCore]
  exact (thm26c_isPGroup_sSup_normal_isPGroup (L := L) p).to_le (Subgroup.normalCore_le _)

/-! ## 2. The assembly: `Thm26cProp` from the p. 221 configuration statement -/

/-- **Bender 1981, pp. 220–221** (the configuration statement of Theorem 2.6, third paragraph).

In the minimal-counterexample setting, with `P` a minimal `H`-invariant odd `p`-subgroup not
centralised by `t`, `M` a coatom with `N_G(P) ≤ M`, and `(V, s, g)` the four-group data of
Bender's Lemma 2.1 / 1.1(iii) (`V ≤ S` a four-group containing `t`, `s ∈ V`, `g ∈ N_G(V) − M`,
`g t g⁻¹ = s`, `C_P(s) ≰ C_P(t)`), the subgroup `P₁ := ⁅⟨t⟩, P ⊓ C_G(s)⁆` satisfies

`N_G(P₁) ⊓ F*(M) ≤ M^g`,

i.e. `M ⇝ M^g` with witness `P₁`.  (`thm26c_of_stepE` is the assembly consuming this.) -/
theorem thm26c_of_stepE
    (stepE : ∀ (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
        (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
        (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
        ∀ (B : Work.GW2.BenderSetup G) (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
          IsPGroup p P → B.H ≤ Subgroup.normalizer (P : Set G) →
          (∀ Q : Subgroup G, Q < P → IsPGroup p Q →
            B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G)) →
          ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) →
          ∀ (M : Subgroup G), IsCoatom M → Subgroup.normalizer (P : Set G) ≤ M →
          ∀ (V : Subgroup G), Work.GW2.IsFourGroup V → V ≤ (B.S : Subgroup G) → B.t ∈ V →
          ∀ (g : G), g ∈ Subgroup.normalizer (V : Set G) → g ∉ M → ∀ s : G,
            g * B.t * g⁻¹ = s → s ∈ V →
            ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
            Subgroup.normalizer
              ((⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ : Subgroup G) : Set G) ⊓
              Work.GW2.fstarIn M ≤ Work.GW2.conjSub g M)
    (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
    (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop) : Work.GW2.Thm26cProp := by
  intro G _ _ hFT hctx B p hp hp2 P hPp hPH
  haveI : IsSimpleGroup G := hctx.simple
  haveI : Fact p.Prime := ⟨hp⟩
  have aux : ∀ n, ∀ P : Subgroup G, Nat.card P = n → IsPGroup p P →
      B.H ≤ Subgroup.normalizer (P : Set G) → P ≤ Subgroup.centralizer ({B.t} : Set G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hcard hPp hPH
      by_contra hnot
      -- `N_G(P)` is a proper subgroup, so it lies in a coatom `M`
      have hNne : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
        intro htop
        have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        haveI := hPn
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hbot | htopP
        · exact hnot (by rw [hbot]; exact bot_le)
        · have h2 : 2 ∣ Nat.card G := by
            have h := orderOf_dvd_natCard B.t
            rwa [B.t_order] at h
          obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥P)).mp hPp
          have h₁ : Nat.card ↥P = Nat.card ↥(⊤ : Subgroup G) := by rw [htopP]
          have h₂ : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
            Nat.card_congr Subgroup.topEquiv.toEquiv
          have hcard' : Nat.card G = p ^ k := by rw [← h₂, ← h₁]; exact hk
          rw [hcard'] at h2
          have hp2' : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
            (Nat.prime_two.dvd_of_dvd_pow h2)
          exact hp2 hp2'.symm
      obtain ⟨M, hM, hNPM⟩ :=
        Work.ASM.exists_coatom_ge_of_ne_top (Subgroup.normalizer (P : Set G)) hNne
      have hHM : B.H ≤ M := le_trans hPH hNPM
      let B' : Work.GW2.BenderSetup G := { B with Hhat := M, Hhat_coatom := hM, H_le_Hhat := hHM }
      have h2 : ¬ Work.GW2.OneInvClassIn M := h21 G hFT hctx B'
      have hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
          B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G) :=
        fun Q hQ hQp hQH =>
          ih (Nat.card Q) (by rw [← hcard]; exact card_lt_card_of_lt hQ) Q rfl hQp hQH
      -- Bender's four-group data
      obtain ⟨V, s, g, htV, hVS, hV4, _hNVM, hsV, _hs1, _hst, hbig, hgN, hgM, hgconj⟩ :=
        bender26c_stepA T hFT G hctx B M hM hHM h2 p hp hp2 P hPp hPH hnot
      -- the configuration statement
      have hE : Subgroup.normalizer
          ((⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ : Subgroup G) : Set G) ⊓
          Work.GW2.fstarIn M ≤ Work.GW2.conjSub g M :=
        stepE T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM
          V hV4 hVS htV g hgN hgM s hgconj hsV hbig
      -- `P ≤ O_p(M)`
      have hPeq : ⁅Subgroup.zpowers B.t, P⁆ = P :=
        b26c_commutator_eq T B p hp hp2 P hPp hPH hmin hnot
      have hPle : P ≤ Work.GW2.pCoreIn p M := by
        rw [← hPeq]
        exact b26c_commutator_le_pCoreIn T hFT hctx B p hp hp2 P hPp hPH M hM hNPM
      -- `P₁ ≤ P ≤ F(M)`
      have hP1leP : (⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ :
          Subgroup G) ≤ P := by
        have htN : Subgroup.zpowers B.t ≤ Subgroup.normalizer (P : Set G) :=
          le_trans (Subgroup.zpowers_le.mpr (bSetup_t_mem_H B)) hPH
        have h1 : ⁅Subgroup.zpowers B.t, P⁆ ≤ P :=
          Subgroup.le_normalizer_iff_commutator_le_right.mp htN
        exact le_trans (Subgroup.commutator_mono le_rfl inf_le_left) h1
      have hP1leF : (⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ :
          Subgroup G) ≤ Work.GW2.fittingIn M :=
        le_trans (le_trans hP1leP hPle) (Work.BMAX.pCoreIn_le_fittingIn M hp)
      -- Bender's relation `M ⇝ M^g`
      have hBRel : Work.GW2.BRel M (Work.GW2.conjSub g M) :=
        ⟨(⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ : Subgroup G), hP1leF, hE⟩
      -- `O(M) ≠ ⊥`, from `1 ≠ P ≤ O_p(M) ≤ O_{2'}(M)`
      have hpodd : Odd p := hp.odd_iff.mpr (by have := hp.two_le; omega)
      have hPcoreOdd : Odd (Nat.card (Work.GW2.pCore p ↥M)) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥(Work.GW2.pCore p ↥M))).mp
          (thm26c_pCore_isPGroup (L := ↥M) p)
        rw [hk]
        exact hpodd.pow
      have hcle : Work.GW2.pCore p ↥M ≤ Work.GW2.oddCore ↥M :=
        (Subgroup.normal_le_normalCore (N := Work.GW2.pCore p ↥M)
            (H := sSup {N : Subgroup ↥M | N.Normal ∧ Odd (Nat.card N)})
            (hN := Work.GW2.pCore_normal p ↥M)).mpr
          (le_sSup ⟨Work.GW2.pCore_normal p ↥M, hPcoreOdd⟩)
      have hO : Work.GW2.oddCoreIn M ≠ ⊥ := by
        intro hO
        have h1 : Work.GW2.pCoreIn p M ≤ Work.GW2.oddCoreIn M := by
          rw [Work.GW2.pCoreIn, Work.GW2.oddCoreIn]
          exact Subgroup.map_mono hcle
        have h2 : P ≤ ⊥ := le_trans hPle (hO ▸ h1)
        have hPbot : P = ⊥ := le_bot_iff.mp h2
        exact hnot (by rw [hPbot]; exact bot_le)
      -- Lemma 2.5 for the setup with `Hhat := M`
      have heq : Work.GW2.conjSub g M = M := h25 G hFT hctx B' g hO hBRel
      have hg : g ∈ M := by
        have hnorm : g ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_of_conjSub_eq heq
        have hMne : M ≠ ⊥ := fun hbot =>
          hO (le_antisymm (hbot ▸ Subgroup.map_subtype_le (Work.GW2.oddCore ↥M)) bot_le)
        have hNM : Subgroup.normalizer (M : Set G) = M :=
          normalizer_eq_of_coatom (K := M) (Z := M) hM le_rfl hMne
            (Subgroup.le_normalizer (H := M))
        rwa [hNM] at hnorm
      exact hgM hg
  exact aux (Nat.card P) P rfl hPp hPH

/-! ## 3. The configuration statement (Bender pp. 220–221)

This is the remaining mathematical content of the step, stated separately so that it can be
proved on its own (it is Bender's "`P₁` centralises `P^g`" plus Lemmas 2.3/2.4). -/

/-- **The “`F(M^g)` not Dedekind” case of step 3, now discharged.**  In the configuration, if
`F(M^g)` is *not* a Dedekind group, then some coatom contains both `N_G(P₁)` and `P^g`.

Formerly this was recorded as the open core of the step (the case
`F(M^g) = F*(M^g) = O_p(M^g)`, a non-abelian `p`-group for an odd `p`, cf.
`Submission/Work/BMAX/NOTES_dedekind_notPGroup_case.md`).  It is now a corollary of Bender's
*actual* p. 221 statement, formalised in `Submission/Work/CORE2A/stepS1_bender.lean`
(`Work.GW21.stepS1Prop_bender : StepS1Prop`): Bender's sentence reads `O_p(H^g) = O_p(H)^g`
with `H = C_G(t)` — the centralizer, **not** the maximal subgroup `Ĥ` — and then (L1) minimality
of `P` with the three-subgroup lemma gives `P ≤ C_G(O_p(H))` while (L2) `1.10.i` inside the
`D`-group `C_G(s)` gives `P₁ ≤ O_p(C_G(s)) = O_p(H)^g`; hence `[P₁, P^g] = 1`, i.e.
`P^g ≤ N_G(P₁)`, and any coatom above `N_G(P₁)` contains `P^g` as well. -/
theorem bender26c_stepW1_notDedekind_local : Work.CORE2A.StepW1CaseNotDedekindProp := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hPp hHN hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs hsV hbig _
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hctx.simple
  -- Bender's centrality: `P^g ≤ N_G(P₁)`
  have hS1 : Work.GW2.conjSub g P ≤
      Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) :=
    Work.GW21.stepS1Prop_bender T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hPp hHN hmin hnot
      M hM hNPM V hV4 hVS htV g hgN hgM s hs.symm hsV hbig
  -- any coatom above `N_G(P₁)` therefore contains `P^g`
  obtain ⟨M', hM', hNM'⟩ :=
    exists_coatom_ge_normalizer_stepP1sub G B P s
      (normalizer_stepP1sub_ne_top G hctx B P s hHN M hM hNPM hbig)
  exact ⟨M', hM', hNM', le_trans hS1 hNM'⟩

/-- **The remaining gap, in its weakest known form** (Bender 1981, p. 221): after
`1.10.i` has produced `P₁ ≤ O_p(Ĥ^g)` and `P^g ≤ O_p(Ĥ)^g`, *some* maximal subgroup `M'`
contains both `N_G(P₁)` and `P^g`; equivalently the join `N_G(P₁) ⊔ P^g` is a proper subgroup
(Bender's “Hence `P^g ⊆ M` for a maximal subgroup `M ⊇ N_G(P₁)`”).

This is *weaker* than the assertion “`P₁` centralizes `P^g`” (which says `P^g ≤ N_G(P₁)`) and
is exactly what the assembly `Work.CORE2A.bender26c_stepE_of_W1` consumes; it is the statement
delegated as `CORE2A/bender26c_stepW1`.

It is assembled here from the case analysis of
`Submission/Work/CORE2A/bender26c_stepW1_case.lean` (`Work.CORE2A.stepW1Prop_of_cases`): the case
“`F(M^g)` Dedekind” is *proved* (`Work.CORE2A.stepW1_of_fitting_dedekind`), and the remaining
case “`F(M^g)` not Dedekind” is `bender26c_stepW1_notDedekind_local` above — the open core of
the step. -/
theorem bender26c_stepW1_local : Work.CORE2A.StepW1Prop :=
  Work.CORE2A.stepW1Prop_of_cases Work.CORE2A.stepW1_of_fitting_dedekind
    bender26c_stepW1_notDedekind_local

/-- The configuration statement of Bender 1981, p. 221, proved from the weaker form
`bender26c_stepW1_local` by the assembly `Work.CORE2A.bender26c_stepE_of_W1`. -/
theorem bender26c_stepE_local :
    ∀ (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
      (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
        IsPGroup p P → B.H ≤ Subgroup.normalizer (P : Set G) →
        (∀ Q : Subgroup G, Q < P → IsPGroup p Q →
          B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G)) →
        ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) →
        ∀ (M : Subgroup G), IsCoatom M → Subgroup.normalizer (P : Set G) ≤ M →
        ∀ (V : Subgroup G), Work.GW2.IsFourGroup V → V ≤ (B.S : Subgroup G) → B.t ∈ V →
        ∀ (g : G), g ∈ Subgroup.normalizer (V : Set G) → g ∉ M → ∀ s : G,
          g * B.t * g⁻¹ = s → s ∈ V →
          ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
            P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
          Subgroup.normalizer
            ((⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ : Subgroup G) : Set G) ⊓
            Work.GW2.fstarIn M ≤ Work.GW2.conjSub g M :=
  Work.CORE2A.bender26c_stepE_of_W1 bender26c_stepW1_local

/-! ## 4. The contract statement

The configuration statement `stepE` is supplied by Bender's *actual* p. 221 argument
(`Work.GW21.stepS1Prop_bender`, in `CORE2A/stepS1_bender.lean`), which uses
`O_p(H^g) = O_p(H)^g` with `H = C_G(t)` — not `Ĥ` — and needs no abelianness of any `O_p(M)`.
The earlier `bender26c_stepW1_local`/`bender26c_stepE_local` chain is kept above as a record; it
is also fully proved (via `bender26c_stepW1_notDedekind_local`, which is now a corollary of
`stepS1Prop_bender`), so this file is `unproved`-free. -/

theorem thm26c (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (h23 : Work.GW2.Lemma23Prop) (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop) :
    Work.GW2.Thm26cProp :=
  thm26c_of_stepE (bender26c_stepE_of_S1 Work.GW21.stepS1Prop_bender) T h21 h23 h24 h25

end Work.CORE2A
