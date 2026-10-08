/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3, leaf 3.7: a Sylow `p`-subgroup is TI

Target: `Work.BSW.S3.s37 : Work.BSW.BSWS37Prop` (Bender 1974, (3.7)): under the case-(ii)
bundle `BSWCase2`, distinct Sylow `p`-subgroups of `G` meet trivially.

The proof is the assembly `s37_of_no_normal_sylow` of two inputs:

* `Work.BSW.S3.s36` — Bender (3.6): for `X ≠ ⊥` a `p`-subgroup, `N_G(X)` has a normal Sylow
  `p`-subgroup;
* `Work.BSW.S3.normalizerNoNormalSylow` — Bender's remark in the proof of (3.7): for `X` a
  *maximal* intersection of two distinct Sylow `p`-subgroups, `N_G(X)` has *no* normal Sylow
  `p`-subgroup.

(The naive variant "a maximal intersection is normal in both Sylows" is false; only the
indirect statement above survives, which is why the argument goes through the normalizer.)

The bundle facts used here are in `Submission/Work/BSW/S3/case2Facts.lean`.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.S3.case2Facts
import Submission.Work.BSW.S3.s36
import Submission.Work.BSW.S3.normalizerNoNormalSylow

namespace Work.BSW.S3

open Subgroup Work.GW2

/-! ## The assembly: (3.6) + Bender's remark ⟹ (3.7)

Suppose `A ≠ B` are Sylow `p`-subgroups meeting nontrivially and choose such a pair with
`X := A ⊓ B` of maximal cardinality.  Bender's remark
(`Work.BSW.S3.normalizerNoNormalSylow`) says that `N_G(X)` has **no** normal Sylow
`p`-subgroup; while (3.6) applied to the nontrivial `p`-subgroup `X` says that `N_G(X)`
**has** one.  Contradiction. -/

/-- If `P ⊴ N` is a Sylow `p`-subgroup of `N` and `A ≤ N` is a `p`-subgroup, then `A ≤ P`:
the unique Sylow `p`-subgroup of `N` absorbs every `p`-subgroup. -/
theorem le_of_subgroupOf_normal_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N P A : Subgroup G} (hN : (P.subgroupOf N).Normal) (hidx : ¬ p ∣ (P.subgroupOf N).index)
    (hPp : IsPGroup p P) (hPle : P ≤ N) (hAle : A ≤ N) (hAp : IsPGroup p A) : A ≤ P := by
  suffices hs : A.subgroupOf N ≤ P.subgroupOf N by
    intro a ha
    have h : (⟨a, hAle ha⟩ : ↥N) ∈ P.subgroupOf N := hs (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp h
  haveI : (P.subgroupOf N).Normal := hN
  have hPsub : IsPGroup p (P.subgroupOf N) := IsPGroup.comap_subtype hPp
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.comap_subtype hAp)
  have hPQ : P.subgroupOf N ≤ (Q : Subgroup ↥N) := IsPGroup.le_sylow_of_normal hPsub Q
  have hcardeq : Nat.card ↥(P.subgroupOf N) = Nat.card ↥(Q : Subgroup ↥N) := by
    have h1 : Nat.card ↥(↑(hPsub.toSylow hidx) : Subgroup ↥N) =
        p ^ (Nat.card ↥N).factorization p := Sylow.card_eq_multiplicity (hPsub.toSylow hidx)
    have h3 : (↑(hPsub.toSylow hidx) : Subgroup ↥N) = P.subgroupOf N :=
      IsPGroup.toSylow_coe (hP1 := hPsub) (hP2 := hidx)
    rw [h3] at h1
    exact h1.trans (Sylow.card_eq_multiplicity Q).symm
  have hQeq : (P.subgroupOf N : Subgroup ↥N) = ↑Q :=
    Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq hcardeq.symm)
  exact hQ.trans (le_of_eq hQeq.symm)

/-- **(3.7) from its inputs.**  `h36` is Bender (3.6) (`BSWS36Prop`); `hNo` is the general fact
that the normalizer of a *maximal* intersection of two distinct Sylow `p`-subgroups has no
normal Sylow `p`-subgroup — Bender's remark in the proof of (3.7), proved in the companion file
`Work.BSW.S3.normalizerNoNormalSylow`.

Let `A ≠ B` be Sylow `p`-subgroups meeting nontrivially and choose such a pair with
`X = A ⊓ B` of maximal cardinality.  By (3.6) applied to the nontrivial `p`-subgroup `X`, the
normalizer `N_G(X)` *has* a normal Sylow `p`-subgroup, contradicting `hNo`. -/
theorem s37_of_no_normal_sylow
    (h36 : Work.BSW.BSWS36Prop)
    (hNo : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime],
      ∀ (A B : Sylow p G), A ≠ B → ∀ X : Subgroup G,
        X = (A : Subgroup G) ⊓ (B : Subgroup G) →
        (∀ C D : Sylow p G, C ≠ D →
          Nat.card ↥((C : Subgroup G) ⊓ (D : Subgroup G)) ≤ Nat.card ↥X) →
        ¬ ∃ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p P ∧
          (P.subgroupOf (Subgroup.normalizer (X : Set G))).Normal ∧
          ¬ p ∣ (P.subgroupOf (Subgroup.normalizer (X : Set G))).index) :
    Work.BSW.BSWS37Prop := by
  intro G instG instFin t s K x p hcase
  haveI : Fact p.Prime := ⟨prime (h := hcase)⟩
  -- it suffices that distinct Sylow `p`-subgroups meet trivially
  have key : ∀ A B : Sylow p G, A ≠ B → (A : Subgroup G) ⊓ (B : Subgroup G) = ⊥ := by
    intro A B hAB
    by_contra hne
    haveI : Fintype (Sylow p G) := Fintype.ofFinite _
    haveI : DecidableEq (Sylow p G) := Classical.decEq _
    -- choose a pair of distinct Sylows with maximal intersection
    let T : Finset (Sylow p G × Sylow p G) := Finset.univ.filter (fun CD => CD.1 ≠ CD.2)
    have hTne : T.Nonempty := by
      refine ⟨(A, B), ?_⟩
      simp [T, hAB]
    obtain ⟨AB, hABT, hmaxAB⟩ := Finset.exists_max_image T
      (fun CD : Sylow p G × Sylow p G =>
        Nat.card ↥((CD.1 : Subgroup G) ⊓ (CD.2 : Subgroup G))) hTne
    have hABne : AB.1 ≠ AB.2 := (Finset.mem_filter.mp hABT).2
    have hmax : ∀ C D : Sylow p G, C ≠ D →
        Nat.card ↥((C : Subgroup G) ⊓ (D : Subgroup G)) ≤
          Nat.card ↥((AB.1 : Subgroup G) ⊓ (AB.2 : Subgroup G)) := by
      intro C D hCD
      exact hmaxAB (C, D) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCD⟩)
    set X : Subgroup G := (AB.1 : Subgroup G) ⊓ (AB.2 : Subgroup G) with hXdef
    have hXp : IsPGroup p X := by
      rw [hXdef]
      exact IsPGroup.to_inf_left AB.1.isPGroup'
    have hXne : X ≠ ⊥ := by
      intro hbot
      have h2 : Nat.card ↥((A : Subgroup G) ⊓ (B : Subgroup G)) ≤ Nat.card ↥X := hmax A B hAB
      rw [hbot, Subgroup.card_bot] at h2
      have hnt : Nontrivial ↥((A : Subgroup G) ⊓ (B : Subgroup G)) := by
        rw [Subgroup.nontrivial_iff_ne_bot]; exact hne
      haveI := hnt
      haveI : Fintype ↥((A : Subgroup G) ⊓ (B : Subgroup G)) := Fintype.ofFinite _
      have h3 : 1 < Nat.card ↥((A : Subgroup G) ⊓ (B : Subgroup G)) := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
      omega
    -- (3.6) applied to the nontrivial `p`-subgroup `X`, contradicting the hypothesis
    obtain ⟨P, D, hPle, _hDle, hPp, hidx, hPnorm, _hsup, _hinf, _gg, _hDconj⟩ :=
      h36 G t s K x p hcase X hXne hXp
    exact hNo G p AB.1 AB.2 hABne X hXdef (fun C D hCD => hmax C D hCD)
      ⟨P, hPle, hPp, hPnorm, hidx⟩
  -- apply to `Q` and to its conjugate `g • Q`
  intro Q g hg
  have hgQ : g • Q ≠ Q := fun h => hg ((Sylow.smul_eq_iff_mem_normalizer).mp h)
  have hkey := key Q (g • Q) (Ne.symm hgQ)
  rw [Sylow.coe_subgroup_smul] at hkey
  exact hkey

theorem s37 : Work.BSW.BSWS37Prop :=
  s37_of_no_normal_sylow Work.BSW.S3.s36
    (fun G _ _ p _ A B hAB X hX hmax =>
      Work.BSW.S3.normalizerNoNormalSylow (G := G) (p := p) hAB hX hmax)

end Work.BSW.S3

