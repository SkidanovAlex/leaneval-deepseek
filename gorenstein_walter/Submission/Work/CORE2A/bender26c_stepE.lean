/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.stepEDefs
import Submission.Work.CORE2A.pCoreIn_conjSub
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE2A.bender26c_stepP1
import Submission.Work.CORE2A.conj_BenderSetup
import Submission.Work.CORE2A.d110i_coatom
import Submission.Work.ASM.Basic
import Submission.Work.BMAX.Bender17i_dedekind_basic

/-!
# CORE2A: Bender 1981, p. 221 — step 3 of Theorem 2.6 from "`P₁` centralizes `P^g`"

This module is the assembly of the remaining step of `Work.GW2.Thm26cProp` (see
`Submission/Work/CORE2A/stepEContext.lean` for the plan of the step and for the state of the
surrounding development).

`bender26c_stepE_of_S1` proves the configuration statement `StepEProp` of Bender 1981, p. 221
(consumed by `Work.CORE2A.thm26c_of_stepE`) from the single input

* `CORE2A/bender26c_stepS1` (`StepS1Prop`): in the configuration, `P₁ := ⁅⟨t⟩, P ⊓ C_G(s)⁆`
  centralizes `P^g` — Bender's “Lying in `O_p(Ĥ^g) = O_p(Ĥ)^g`, `P₁` centralizes `P^g`”.

Everything else is proved here, from

* `Work.CORE2A.bender26c_stepP1` (`P₁ ≤ O_p(M^g)`),
* `Work.CORE2A.d110i_coatom` (Bender 1.10(i) inside a coatom),
* `Work.CORE2A.conj_BenderSetup` (the conjugate of a Bender setup),
* the hypotheses `h23` (Bender's Lemma 2.3 = Bender 1970 §1.6/1.7) and `h24` (Lemma 2.4,
  Glauberman's `Z(J)`-theorem).

The argument is the one recorded in Bender's paper: with `M'` a coatom containing `N_G(P₁)`
(and, thanks to the input, also `P^g`),

* `d110i_coatom` in `M'` with the involution `s` gives `P^g = ⁅P^g, ⟨s⟩⁆ ≤ O_p(M') ≤ F(M')`,
  so `M' ⇝ M^g` with witness `P^g`;
* `P₁ ≤ O_p(M^g)` and `N_G(P₁) ≤ M'` give `M^g ⇝ M'` with witness `P₁`;
* Lemma 2.3(iii) for the conjugated setup `B^g` (`Ĥ := M^g`, `t := s`) gives `M^g = M'` unless
  both `F*(M^g)` and `F*(M')` are `q`-groups; `q = 2` is impossible because
  `1 ≠ P^g ≤ F*(M^g)` is a `p`-group with `p` odd, and Lemma 2.4 (`h24`) then gives `M^g = M'`;
* so `N_G(P₁) ≤ M^g`, and the conclusion `N_G(P₁) ⊓ F*(M) ≤ M^g` follows.
-/

open scoped MatrixGroups commutatorElement

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. The two statements -/

/-- Bender 1981, p. 221: `P₁ := ⁅⟨t⟩, P ⊓ C_G(s)⁆` centralizes `P^g`, i.e. `P^g ≤ N_G(P₁)`.

This is the input of `bender26c_stepE_of_S1`; it is the statement requested as
`CORE2A/bender26c_stepS1`. -/
def StepS1Prop : Prop :=
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
        s = g * B.t * g⁻¹ → s ∈ V →
        ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
          P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
        Work.GW2.conjSub g P ≤
          Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G)

/-- Bender 1981, p. 221, the configuration statement of step 3 of Theorem 2.6 (the `stepE`
argument of `Work.CORE2A.thm26c_of_stepE`): `N_G(P₁) ⊓ F*(M) ≤ M^g` with
`P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆`. -/
def StepEProp : Prop :=
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
        Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ⊓
          Work.GW2.fstarIn M ≤ Work.GW2.conjSub g M

/-! ## 2. Elementary helpers -/

/-- `x` normalizes `K^g` if and only if `g⁻¹ x g` normalizes `K`. -/
theorem mem_normalizer_conjSub_iff {G : Type*} [Group G] {K : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (Work.GW2.conjSub g K : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have h1 := h (g * z * g⁻¹)
    simp only [Work.CORE2A.mem_conjSub_iff] at h1
    have h2 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have h3 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g
        = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by group
    rw [h2, h3] at h1
    exact h1
  · intro h y
    rw [Work.CORE2A.mem_conjSub_iff, Work.CORE2A.mem_conjSub_iff]
    rw [show g⁻¹ * (x * y * x⁻¹) * g
        = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ by group]
    exact h (g⁻¹ * y * g)

/-- If `a` and `b` commute then `b` fixes `a` by conjugation. -/
theorem conj_eq_of_mul_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    b * a * b⁻¹ = a := by
  rw [← h]
  group

/-- Every element normalizes the centralizer of itself. -/
theorem mem_normalizer_centralizer_self {G : Type*} [Group G] (s : G) :
    s ∈ Subgroup.normalizer (Subgroup.centralizer ({s} : Set G)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [show s * x * s⁻¹ = x by rw [← hx']; group]
    exact hx
  · intro hx
    have hy : s * (s * x * s⁻¹) * s⁻¹ = s * x * s⁻¹ := by
      have hxs' : (s * x * s⁻¹) * s = s * (s * x * s⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [← hxs']; group
    have hx' : x = s * x * s⁻¹ := by
      calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
        _ = s⁻¹ * (s * (s * x * s⁻¹) * s⁻¹) * s := by rw [hy]
        _ = s * x * s⁻¹ := by group
    rw [hx']
    exact hx

/-- An element normalizing two subgroups normalizes their intersection. -/
theorem mem_normalizer_inf {G : Type*} [Group G] {A Bb : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (Bb : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ Bb : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hyA, hyB⟩
    exact ⟨(hA y).mp hyA, (hB y).mp hyB⟩
  · rintro ⟨hyA, hyB⟩
    exact ⟨(hA y).mpr hyA, (hB y).mpr hyB⟩

/-- An element normalizing two subgroups normalizes their commutator. -/
theorem mem_normalizer_commutator {G : Type*} [Group G] {A Bb : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (Bb : Set G)) :
    x ∈ Subgroup.normalizer ((⁅A, Bb⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

/-- If `C_G(t) ≤ N_G(K)` and `s = g t g⁻¹`, then `C_G(s) ≤ N_G(K^g)`. -/
theorem centralizer_le_normalizer_conjSub {G : Type*} [Group G] {K : Subgroup G} {g t s : G}
    (hconj : g * t * g⁻¹ = s)
    (h : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (Work.GW2.conjSub g K : Set G) := by
  intro x hx
  rw [mem_normalizer_conjSub_iff]
  refine h ?_
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc (g⁻¹ * x * g) * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (x * s) * g := by rw [hconj]
    _ = g⁻¹ * (s * x) * g := by rw [← hx]
    _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hconj]
    _ = t * (g⁻¹ * x * g) := by group

/-! ## 3. The assembly -/

/-- Bender 1981, p. 221: there is a coatom `M'` containing both `N_G(P₁)` and `P^g`
(Bender's “Hence `P^g ⊆ M` for a maximal subgroup `M ⊇ N_G(P₁)`”).

This is *weaker* than `StepS1Prop` (which says `P^g ≤ N_G(P₁)`) and is exactly what the assembly
`bender26c_stepE_of_W1` consumes. -/
def StepW1Prop : Prop :=
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
        ∃ M' : Subgroup G, IsCoatom M' ∧
          Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M' ∧
          Work.GW2.conjSub g P ≤ M'

/-- `StepS1Prop` implies `StepW1Prop`: if `P^g` normalises `P₁`, then any coatom containing
`N_G(P₁)` contains `P^g`.  (The existence of such a coatom uses `P₁ ≠ ⊥`, which follows from
`hbig`.) -/
theorem stepW1_of_stepS1 (hS1 : StepS1Prop) : StepW1Prop := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
    g hgN hgM s hgconj hsV hbig
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hctx.simple
  set P1 : Subgroup G := Work.CORE2A.stepP1sub B P s with hP1def
  have hPM : P ≤ M := fun x hx => hNPM (Subgroup.le_normalizer hx)
  have hP1leP : P1 ≤ P := by
    rw [hP1def, Work.CORE2A.stepP1sub]
    have htN : Subgroup.zpowers B.t ≤ Subgroup.normalizer (P : Set G) :=
      le_trans (Subgroup.zpowers_le.mpr (bSetup_t_mem_H B)) hPH
    exact le_trans (Subgroup.commutator_mono le_rfl inf_le_left)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp htN)
  have hP1leM : P1 ≤ M := le_trans hP1leP hPM
  have hP1ne : P1 ≠ ⊥ := by
    intro hbot
    apply hbig
    intro x hx
    obtain ⟨hxP, hxs⟩ := hx
    have hmem : ⁅B.t, x⁆ ∈ P1 := by
      rw [hP1def, Work.CORE2A.stepP1sub]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers B.t) ⟨hxP, hxs⟩
    rw [hbot] at hmem
    have h1 : ⁅B.t, x⁆ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : B.t * x = x * B.t := commutatorElement_eq_one_iff_mul_comm.mp h1
    exact ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩
  have hNne : Subgroup.normalizer (P1 : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : P1.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P1 with h | h
    · exact hP1ne h
    · exact hM.ne_top (top_le_iff.mp (h ▸ hP1leM))
  obtain ⟨M', hM'coat, hNM'⟩ :=
    Work.ASM.exists_coatom_ge_of_ne_top (Subgroup.normalizer (P1 : Set G)) hNne
  refine ⟨M', hM'coat, hNM', le_trans ?_ hNM'⟩
  exact hS1 T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
    g hgN hgM s hgconj.symm hsV hbig

/-- Bender 1981, p. 221, the local-analysis input behind “Lying in
`O_p(Ĥ^g) = O_p(Ĥ)^g`, `P₁` centralizes `P^g`”: in the configuration the `p`-core `O_p(M^g)` of
the conjugate coatom is abelian.

This is the instance of the area `BMAX`'s recorded open core `pCore_abelian_or_fitting_pgroup`
(abelianness of an odd `p`-core of a maximal subgroup): it implies `StepS1Prop` by
`stepS1_of_pCoreIn_abelian`, hence `StepEProp` by `bender26c_stepE_of_pCoreIn_abelian`. -/
def StepAbelProp : Prop :=
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
        IsMulCommutative ↥(Work.GW2.pCoreIn p (Work.GW2.conjSub g M))

/-- `P^g ≤ O_p(M^g)` (Bender's “`P^g ⊆ O_p(Ĥ)^g = O_p(Ĥ^g)`”, i.e. Bender 1.10(i) in the
coatom `M^g` with the involution `s`). -/
theorem conjSub_le_pCoreIn_conj (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hPp : IsPGroup p P)
    (hPH : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G))
    (s : G) (hs : s = g * B.t * g⁻¹) (hsV : s ∈ V) :
    Work.GW2.conjSub g P ≤ Work.GW2.pCoreIn p (Work.GW2.conjSub g M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : P ≤ M := fun x hx => hNPM (Subgroup.le_normalizer hx)
  have hst : B.t * s = s * B.t := by
    have hc : IsMulCommutative ↥V := IsFourGroup.isMulCommutative' hV4
    have h2 : (⟨B.t, htV⟩ : ↥V) * ⟨s, hsV⟩ = ⟨s, hsV⟩ * ⟨B.t, htV⟩ :=
      @mul_comm' ↥V _ hc ⟨B.t, htV⟩ ⟨s, hsV⟩
    exact Subtype.ext_iff.mp h2
  have hsH : s ∈ B.H := bSetup_S_le_H B (hVS hsV)
  have hPgP : IsPGroup p (Work.GW2.conjSub g P) := by
    rw [Work.CORE2A.conjSub_eq_map]
    exact hPp.map (MulAut.conj g).toMonoidHom
  have hs2 : orderOf s = 2 := by
    rw [hs, ← MulAut.conj_apply]
    exact (BenderConj.orderOf_mul_conj g B.t).trans B.t_order
  have hcen : Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (Work.GW2.conjSub g P : Set G) :=
    centralizer_le_normalizer_conjSub hs.symm hPH
  have hPgM : Work.GW2.conjSub g P ≤ Work.GW2.conjSub g M := Work.CORE2A.conjSub_mono hPM g
  have hsMg : s ∈ Work.GW2.conjSub g M := by
    rw [Work.CORE2A.mem_conjSub_iff, show g⁻¹ * s * g = B.t by rw [hs]; group]
    exact hNPM (hPH (bSetup_t_mem_H B))
  have hdMg : ⁅Work.GW2.conjSub g P, Subgroup.zpowers s⁆ ≤
      Work.GW2.pCoreIn p (Work.GW2.conjSub g M) :=
    d110i_coatom T hFT G hctx s hs2 p hp hp2 (Work.GW2.conjSub g P) hPgP
      (Work.GW2.conjSub g M) (BenderConj.isCoatom_conjSub hM g) hsMg hPgM
      (le_trans inf_le_left hcen)
  have hPeq : ⁅Subgroup.zpowers B.t, P⁆ = P :=
    b26c_commutator_eq T B p hp hp2 P hPp hPH hmin hnot
  have hL : ⁅Work.GW2.conjSub g P, Subgroup.zpowers s⁆ = Work.GW2.conjSub g P := by
    have hzs : Subgroup.zpowers s = Work.GW2.conjSub g (Subgroup.zpowers B.t) := by
      rw [hs, ← MulAut.conj_apply]
      exact (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom B.t).symm
    rw [hzs, Work.GW2.conjSub, Work.GW2.conjSub, ← Subgroup.map_commutator,
      Subgroup.commutator_comm, hPeq]
  exact hL ▸ hdMg

/-- Bender's justification, made precise: if `O_p(M^g)` is abelian then `P₁` centralizes `P^g`
(both `P₁` — `bender26c_stepP1` — and `P^g` — `conjSub_le_pCoreIn_conj` — lie in `O_p(M^g)`). -/
theorem stepS1_of_pCoreIn_abelian (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : s = g * B.t * g⁻¹) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G)))
    (hA : IsMulCommutative ↥(Work.GW2.pCoreIn p (Work.GW2.conjSub g M))) :
    Work.GW2.conjSub g P ≤
      Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) := by
  set A : Subgroup G := Work.GW2.pCoreIn p (Work.GW2.conjSub g M) with hAdef
  have hP1leA : Work.CORE2A.stepP1sub B P s ≤ A := by
    rw [hAdef, Work.CORE2A.stepP1sub]
    exact bender26c_stepP1 T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig
  have hPgleA : Work.GW2.conjSub g P ≤ A := by
    rw [hAdef]
    exact conjSub_le_pCoreIn_conj T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN s hs hsV
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer
    ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxA : x ∈ A := hPgleA hx
  have hyA : y ∈ A := hP1leA hy
  have hcomm : (⟨y, hyA⟩ : ↥A) * ⟨x, hxA⟩ = (⟨x, hxA⟩ : ↥A) * ⟨y, hyA⟩ := mul_comm' _ _
  simpa using congrArg Subtype.val hcomm

/-- The assembly of `StepEProp` from the weaker input `StepW1Prop` (cf.
`bender26c_stepE_of_S1`).

The argument is Bender's: `d110i_coatom` in `M'` with the involution `s` gives
`P^g = ⁅P^g, ⟨s⟩⁆ ≤ O_p(M') ≤ F(M')`, so `M' ⇝ M^g` with witness `P^g`; `P₁ ≤ O_p(M^g)` and
`N_G(P₁) ≤ M'` give `M^g ⇝ M'` with witness `P₁`; Lemma 2.3(iii) for the conjugate setup `B^g`
(`Ĥ := M^g`, `t := s`) gives `M^g = M'` unless both `F*(M^g)`, `F*(M')` are `q`-groups, and
`q = 2` is impossible since `1 ≠ P^g ≤ F*(M^g)` is a `p`-group with `p` odd; Lemma 2.4 then
gives `M^g = M'`, whence `N_G(P₁) ≤ M^g`. -/
theorem bender26c_stepE_of_W1 (hW1 : StepW1Prop) : StepEProp := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
    g hgN hgM s hgconj hsV hbig
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hctx.simple
  -- `P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆`
  set P1 : Subgroup G := Work.CORE2A.stepP1sub B P s with hP1def
  have hHM : B.H ≤ M := le_trans hPH hNPM
  have hPM : P ≤ M := fun x hx => hNPM (Subgroup.le_normalizer hx)
  -- (1) `t` and `s` commute (`V` is a four-group)
  have hst : B.t * s = s * B.t := by
    have hc : IsMulCommutative ↥V := IsFourGroup.isMulCommutative' hV4
    have h2 : (⟨B.t, htV⟩ : ↥V) * ⟨s, hsV⟩ = ⟨s, hsV⟩ * ⟨B.t, htV⟩ :=
      @mul_comm' ↥V _ hc ⟨B.t, htV⟩ ⟨s, hsV⟩
    exact Subtype.ext_iff.mp h2
  have hsH : s ∈ B.H := bSetup_S_le_H B (hVS hsV)
  -- (2) `s ∈ N_G(P₁)`
  have hszt : s ∈ Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    show MulAut.conj s B.t = B.t
    rw [MulAut.conj_apply, conj_eq_of_mul_comm hst]
  have hsC : s ∈ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (hPH hsH) (mem_normalizer_centralizer_self s)
  have hsN1 : s ∈ Subgroup.normalizer (P1 : Set G) := by
    rw [hP1def, Work.CORE2A.stepP1sub]
    exact mem_normalizer_commutator hszt hsC
  -- (3) the coatom `M'`: by the input it contains `N_G(P₁)` and `P^g`
  obtain ⟨M', hM'coat, hNM', hPgM'⟩ :=
    hW1 T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
      g hgN hgM s hgconj hsV hbig
  have hP1M' : P1 ≤ M' := le_trans Subgroup.le_normalizer hNM'
  have hsM' : s ∈ M' := hNM' hsN1
  -- (5) `P^g` is a nontrivial `p`-group and `C_G(s) ≤ N_G(P^g)`
  have hPgP : IsPGroup p (Work.GW2.conjSub g P) := by
    rw [Work.CORE2A.conjSub_eq_map]
    exact hPp.map (MulAut.conj g).toMonoidHom
  have hPne : P ≠ ⊥ := by
    intro hbot
    exact hnot (by rw [hbot]; exact bot_le)
  have hPgne : Work.GW2.conjSub g P ≠ ⊥ := fun h =>
    hPne (Work.CORE2A.conjSub_injective g (by rw [h, Work.CORE2A.conjSub_bot]))
  have hs2 : orderOf s = 2 := by
    rw [← hgconj, ← MulAut.conj_apply]
    exact (BenderConj.orderOf_mul_conj g B.t).trans B.t_order
  have hcen : Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (Work.GW2.conjSub g P : Set G) :=
    centralizer_le_normalizer_conjSub hgconj hPH
  -- (6) `1.10(i)` inside `M^g` and inside `M'`, with the involution `s`
  have hPgM : Work.GW2.conjSub g P ≤ Work.GW2.conjSub g M := Work.CORE2A.conjSub_mono hPM g
  have hsMg : s ∈ Work.GW2.conjSub g M := by
    rw [Work.CORE2A.mem_conjSub_iff, show g⁻¹ * s * g = B.t by rw [← hgconj]; group]
    exact hNPM (hPH (bSetup_t_mem_H B))
  have hdMg : ⁅Work.GW2.conjSub g P, Subgroup.zpowers s⁆ ≤
      Work.GW2.pCoreIn p (Work.GW2.conjSub g M) :=
    d110i_coatom T hFT G hctx s hs2 p hp hp2 (Work.GW2.conjSub g P) hPgP
      (Work.GW2.conjSub g M) (BenderConj.isCoatom_conjSub hM g) hsMg hPgM
      (le_trans inf_le_left hcen)
  have hdM' : ⁅Work.GW2.conjSub g P, Subgroup.zpowers s⁆ ≤ Work.GW2.pCoreIn p M' :=
    d110i_coatom T hFT G hctx s hs2 p hp hp2 (Work.GW2.conjSub g P) hPgP
      M' hM'coat hsM' hPgM' (le_trans inf_le_left hcen)
  -- (7) `⁅P^g, ⟨s⟩⁆ = P^g` (since `P = ⁅⟨t⟩, P⁆`)
  have hPeq : ⁅Subgroup.zpowers B.t, P⁆ = P :=
    b26c_commutator_eq T B p hp hp2 P hPp hPH hmin hnot
  have hL : ⁅Work.GW2.conjSub g P, Subgroup.zpowers s⁆ = Work.GW2.conjSub g P := by
    have hzs : Subgroup.zpowers s = Work.GW2.conjSub g (Subgroup.zpowers B.t) := by
      rw [← hgconj, ← MulAut.conj_apply]
      exact (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom B.t).symm
    rw [hzs, Work.GW2.conjSub, Work.GW2.conjSub, ← Subgroup.map_commutator,
      Subgroup.commutator_comm, hPeq]
  have hPgA : Work.GW2.conjSub g P ≤ Work.GW2.pCoreIn p (Work.GW2.conjSub g M) := hL ▸ hdMg
  have hPgFstar : Work.GW2.conjSub g P ≤ Work.GW2.fstarIn (Work.GW2.conjSub g M) :=
    le_trans hPgA (le_trans (Work.BMAX.pCoreIn_le_fittingIn _ hp)
      (Subgroup.map_mono le_sup_left))
  -- (8) the two `⇝`-relations
  have hPgleF' : Work.GW2.conjSub g P ≤ Work.GW2.fittingIn M' :=
    le_trans (hL ▸ hdM') (Work.BMAX.pCoreIn_le_fittingIn M' hp)
  have hNconj_le : Subgroup.normalizer (Work.GW2.conjSub g P : Set G) ≤
      Work.GW2.conjSub g M := by
    intro x hx
    rw [Work.CORE2A.mem_conjSub_iff]
    exact hNPM (mem_normalizer_conjSub_iff.mp hx)
  have hBrel1 : Work.GW2.BRel M' (Work.GW2.conjSub g M) :=
    ⟨Work.GW2.conjSub g P, hPgleF', le_trans inf_le_left hNconj_le⟩
  have hP1leF : P1 ≤ Work.GW2.fittingIn (Work.GW2.conjSub g M) := by
    have h := bender26c_stepP1 T hFT G hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hgconj.symm hsV hbig
    rw [hP1def, Work.CORE2A.stepP1sub]
    exact le_trans h (Work.BMAX.pCoreIn_le_fittingIn _ hp)
  have hBrel2 : Work.GW2.BRel (Work.GW2.conjSub g M) M' :=
    ⟨P1, hP1leF, le_trans inf_le_left hNM'⟩
  -- (9) the conjugate setup `B^g` (`t := s`) with `Ĥ := M^g`
  obtain ⟨Bg, _hBgS, _hBgS0, hBgt, _hBgHhat⟩ := conj_BenderSetup B g
  have hBgt2 : Bg.t = s := by rw [hBgt, hgconj]
  have hCsM : Subgroup.centralizer ({Bg.t} : Set G) ≤ Work.GW2.conjSub g M := by
    rw [hBgt2, ← hgconj, BenderConj.centralizer_conj g B.t]
    exact Work.CORE2A.conjSub_mono hHM g
  have hcoatMg : IsCoatom (Work.GW2.conjSub g M) := BenderConj.isCoatom_conjSub hM g
  let B₂ : Work.GW2.BenderSetup G :=
    { Bg with
      Hhat := Work.GW2.conjSub g M
      Hhat_coatom := hcoatMg
      H_le_Hhat := hCsM }
  -- (10) Lemmas 2.3(iii) and 2.4 for the pair `(M^g, M')`
  have h233 := (h23 G hFT hctx B₂ M' hM'coat.ne_top hBrel2).2.2 hM'coat hBrel1
  have hgoal : Work.GW2.conjSub g M = M' := by
    rcases h233 with hEq | ⟨q, hqprime, hqF1, hqF2⟩
    · exact hEq
    · -- the exceptional case of Lemma 2.3(iii) is killed by Lemma 2.4
      have hq2 : q ≠ 2 := by
        intro hq2
        have hqP : IsPGroup q (Work.GW2.conjSub g P) := hqF1.to_le hPgFstar
        have h2P : IsPGroup 2 (Work.GW2.conjSub g P) := by rw [hq2] at hqP; exact hqP
        have hdisj : Disjoint (Work.GW2.conjSub g P) (Work.GW2.conjSub g P) :=
          IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _ h2P hPgP
        refine hPgne ?_
        have h1 := hdisj.eq_bot
        rwa [inf_idem] at h1
      exact h24 G hFT hctx B₂ M' hM'coat hBrel2 q hqprime hq2 hqF1 hqF2
  rw [hgoal]
  exact le_trans inf_le_left hNM'

/-- The assembly of `StepEProp` from Bender's assertion `bender26c_stepS1`
(`P₁` centralizes `P^g`): `bender26c_stepE_of_W1` composed with `stepW1_of_stepS1`. -/
theorem bender26c_stepE_of_S1 (hS1 : StepS1Prop) : StepEProp :=
  bender26c_stepE_of_W1 (stepW1_of_stepS1 hS1)

/-- `StepAbelProp` implies `StepS1Prop` (Bender's printed justification). -/
theorem stepS1_of_stepAbel (h : StepAbelProp) : StepS1Prop := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
    g hgN hgM s hs hsV hbig
  exact stepS1_of_pCoreIn_abelian T hFT G hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs hsV hbig (h T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hPp hPH
      hmin hnot M hM hNPM V hV4 hVS htV g hgN hgM s hs.symm hsV hbig)

/-- `StepEProp` from the abelianness of `O_p(M^g)` (`StepAbelProp`) — Bender's route. -/
theorem bender26c_stepE_of_pCoreIn_abelian (h : StepAbelProp) : StepEProp :=
  bender26c_stepE_of_W1 (stepW1_of_stepS1 (stepS1_of_stepAbel h))


/-- The `M`-side of Bender's justification: if `O_p(M)` is abelian then `P₁` centralizes `P^g`.

Indeed `P ≤ O_p(M)` (`b26c_commutator_le_pCoreIn`) and `P₁^{g⁻¹} ≤ O_p(M)` (`bender26c_stepP1`
together with `pCoreIn_conjSub`), so `P` and `P₁^{g⁻¹}` commute; conjugating by `g` gives
`⁅P₁, P^g⁆ = ⊥`, i.e. `P^g ≤ C_G(P₁) ≤ N_G(P₁)`.

Together with `stepS1_of_pCoreIn_abelian` (the `M^g`-side) this covers both disjuncts of
`CORE2A/stepS1_of_pCore_abelian`: **if either `O_p(M)` or `O_p(M^g)` is abelian, then `P₁`
centralizes `P^g`.** -/
theorem stepS1_of_pCoreIn_abelian_M (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hPp : IsPGroup p P)
    (hPH : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : s = g * B.t * g⁻¹) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G)))
    (hA : IsMulCommutative ↥(Work.GW2.pCoreIn p M)) :
    Work.GW2.conjSub g P ≤
      Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) := by
  set A : Subgroup G := Work.GW2.pCoreIn p M with hAdef
  have hPleA : P ≤ A := by
    rw [hAdef, ← b26c_commutator_eq T B p hp hp2 P hPp hPH hmin hnot]
    exact b26c_commutator_le_pCoreIn T hFT hctx B p hp hp2 P hPp hPH M hM hNPM
  have hP1cj : Work.GW2.conjSub g⁻¹ (Work.CORE2A.stepP1sub B P s) ≤ A := by
    have h := bender26c_stepP1 T hFT G hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig
    have h2 := Work.CORE2A.conjSub_mono h g⁻¹
    rw [pCoreIn_conjSub, Work.CORE2A.conjSub_inv_conjSub] at h2
    rw [hAdef]
    exact h2
  -- `P` and `P₁^{g⁻¹}` are both inside the abelian group `A`, so they commute
  have hcomm : ⁅Work.GW2.conjSub g⁻¹ (Work.CORE2A.stepP1sub B P s), P⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxA : x ∈ A := hP1cj hx
    have hyA : y ∈ A := hPleA hy
    have hc : (⟨y, hyA⟩ : ↥A) * ⟨x, hxA⟩ = (⟨x, hxA⟩ : ↥A) * ⟨y, hyA⟩ :=
      @mul_comm' ↥A _ hA ⟨y, hyA⟩ ⟨x, hxA⟩
    exact congrArg Subtype.val hc
  have hcomm2 : ⁅Work.CORE2A.stepP1sub B P s, Work.GW2.conjSub g P⁆ = ⊥ := by
    have hf : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom
        = MonoidHom.id G :=
      MonoidHom.ext (fun x => by
        show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
        group)
    have h := congrArg (Work.GW2.conjSub g) hcomm
    rw [Work.CORE2A.conjSub_bot, Work.GW2.conjSub, Subgroup.map_commutator, Work.GW2.conjSub,
      Subgroup.map_map, hf, Subgroup.map_id] at h
    rw [Work.GW2.conjSub]
    exact h
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [← Subgroup.commutator_comm] at hcomm2
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm2)

end Work.CORE2A
