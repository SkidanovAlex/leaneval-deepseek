/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: the `p`-core API under conjugation (`O_p(K^g) = O_p(K)^g`)

A clash-free home for the elementary facts about `Work.GW2.pCoreIn` that this area needs and that
currently live only inside modules which cannot all be imported together
(`bender26c_stepB_fixed.lean` declares `le_pCore_of_normal_isPGroup` and `pCoreIn_conj` and
clashes with `fstar_eq_pCore_of_isPGroup.lean`):

* `isPGroup_sSup_normal_isPGroup`, `pCore_isPGroup` — `O_p` is a `p`-group;
* `le_normalizer_map_subtype_of_normal`, `le_normalizer_pCoreIn` — `O_p(K) ⊴ K`;
* `le_pCoreIn_of_normal_isPGroup` — a normal `p`-subgroup of `K` lies in `O_p(K)`;
* `normal_subgroupOf_conjSub` — conjugating a normal pair `N ⊴ K` by `g` keeps it normal.

These are the ingredients of `O_p(K^g) = O_p(K)^g` used by the step-3 work of
`Submission/Work/CORE2A/bender26c_stepE.lean` (cf. `NOTES_CORE2A_thm26c.md`), e.g. to transport
`P₁ ≤ O_p(M^g)` back to `P₁^{g⁻¹} ≤ O_p(M)`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. `O_p` is a `p`-group -/

/-- The join of the normal `p`-subgroups of a group is a `p`-group. -/
theorem isPGroup_sSup_normal_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(sSup {N : Subgroup L | N.Normal ∧ IsPGroup p N}) :=
  Sylow.sSup_of_normal _ (fun _ hN => hN.2) (fun _ hN => hN.1)

/-- `O_p(L)` is a `p`-group. -/
theorem pCore_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(Work.GW2.pCore p L) := by
  rw [Work.GW2.pCore]
  exact (isPGroup_sSup_normal_isPGroup (L := L) p).to_le (Subgroup.normalCore_le _)

/-- `O_p(K)` is a `p`-group. -/
theorem pCoreIn_isPGroup_gen {G : Type*} [Group G] (p : ℕ) (K : Subgroup G) :
    IsPGroup p (Work.GW2.pCoreIn p K) := by
  rw [Work.GW2.pCoreIn]
  exact (pCore_isPGroup (L := ↥K) p).map K.subtype

/-! ## 2. `O_p(K)` is normal in `K` -/

/-- If `M ⊴ ↥K` then `K` normalizes the image of `M` in the ambient group. -/
theorem le_normalizer_map_subtype_of_normal {G : Type*} [Group G] {K : Subgroup G}
    {M : Subgroup ↥K} (hM : M.Normal) :
    K ≤ Subgroup.normalizer ((M.map K.subtype : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨(⟨x, hx⟩ : ↥K) * m * (⟨x, hx⟩ : ↥K)⁻¹, hM.conj_mem m hm (⟨x, hx⟩ : ↥K), rfl⟩
  · intro hy
    obtain ⟨m, hm, hmx⟩ := hy
    refine ⟨(⟨x, hx⟩ : ↥K)⁻¹ * m * (⟨x, hx⟩ : ↥K), ?_, ?_⟩
    · simpa using hM.conj_mem m hm (⟨x, hx⟩ : ↥K)⁻¹
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hmx ⊢
    rw [hmx]
    group

/-- `O_p(K)` is a normal subgroup of `K`. -/
theorem le_normalizer_pCoreIn {G : Type*} [Group G] (K : Subgroup G) (p : ℕ) :
    K ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p K : Subgroup G) : Set G) := by
  rw [Work.GW2.pCoreIn]
  exact le_normalizer_map_subtype_of_normal (Work.GW2.pCore_normal p ↥K)

/-! ## 3. Normal `p`-subgroups lie in `O_p` -/

/-- A normal `p`-subgroup of `K` lies in `O_p(K)`. -/
theorem le_pCoreIn_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ} {K N : Subgroup G}
    (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) (hp : IsPGroup p N) :
    N ≤ Work.GW2.pCoreIn p K := by
  rw [Work.GW2.pCoreIn]
  have hp' : IsPGroup p ↥(N.subgroupOf K) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hle : N.subgroupOf K ≤ Work.GW2.pCore p ↥K :=
    (Subgroup.normal_le_normalCore (N := N.subgroupOf K)
      (H := sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) (hN := hN)).mpr
      (le_sSup ⟨hN, hp'⟩)
  calc N = (N.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hNK).symm
    _ ≤ (Work.GW2.pCore p ↥K).map K.subtype := Subgroup.map_mono hle

/-! ## 4. Conjugating a normal pair keeps it normal -/

/-- Conjugating a normal pair `N ⊴ K` by `g` keeps it normal: `N^g ⊴ K^g`. -/
theorem normal_subgroupOf_conjSub {G : Type*} [Group G] {K N : Subgroup G} (g : G)
    (hN : (N.subgroupOf K).Normal) :
    ((Work.GW2.conjSub g N).subgroupOf (Work.GW2.conjSub g K)).Normal := by
  refine ⟨fun a ha b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [Work.CORE2A.mem_conjSub_iff] at ha ⊢
  have haK : g⁻¹ * (a : G) * g ∈ K := Work.CORE2A.mem_conjSub_iff.mp a.2
  have hb : g⁻¹ * (b : G) * g ∈ K := Work.CORE2A.mem_conjSub_iff.mp b.2
  have h1 : (⟨g⁻¹ * (a : G) * g, haK⟩ : ↥K) ∈ N.subgroupOf K := ha
  have h2 := hN.conj_mem (⟨g⁻¹ * (a : G) * g, haK⟩ : ↥K) h1 (⟨g⁻¹ * (b : G) * g, hb⟩ : ↥K)
  rw [Subgroup.mem_subgroupOf] at h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at h2 ⊢
  convert h2 using 1
  group

/-! ## 5. `O_p(K^g) = O_p(K)^g` -/

/-- One inclusion: `O_p(K)^g ≤ O_p(K^g)`. -/
theorem conjSub_pCoreIn_le {G : Type} [Group G] [Finite G] (g : G) (p : ℕ) (K : Subgroup G) :
    Work.GW2.conjSub g (Work.GW2.pCoreIn p K) ≤
      Work.GW2.pCoreIn p (Work.GW2.conjSub g K) := by
  refine le_pCoreIn_of_normal_isPGroup ?_ ?_ ?_
  · have h1 : Work.GW2.pCoreIn p K ≤ K := Subgroup.map_subtype_le _
    exact Work.CORE2A.conjSub_mono h1 g
  · have h1 : Work.GW2.pCoreIn p K ≤ K := Subgroup.map_subtype_le _
    have h2 : ((Work.GW2.pCoreIn p K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h1).mpr (le_normalizer_pCoreIn K p)
    exact normal_subgroupOf_conjSub g h2
  · exact (pCoreIn_isPGroup_gen p K).of_equiv (Subgroup.equivMapOfInjective _
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)

/-- **`O_p` commutes with conjugation**: `O_p(K^g) = O_p(K)^g`. -/
theorem pCoreIn_conjSub {G : Type} [Group G] [Finite G] (g : G) (p : ℕ) (K : Subgroup G) :
    Work.GW2.pCoreIn p (Work.GW2.conjSub g K) =
      Work.GW2.conjSub g (Work.GW2.pCoreIn p K) := by
  refine le_antisymm ?_ (conjSub_pCoreIn_le g p K)
  rw [← Work.CORE2A.conjSub_le_conjSub_iff (g := g⁻¹), Work.CORE2A.conjSub_inv_conjSub]
  have h := conjSub_pCoreIn_le g⁻¹ p (Work.GW2.conjSub g K)
  rwa [Work.CORE2A.conjSub_inv_conjSub] at h

end Work.CORE2A
