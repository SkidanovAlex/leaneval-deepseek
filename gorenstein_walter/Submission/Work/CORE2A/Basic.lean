/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.CORE2A.Defs
import Submission.Work.ASM.oddCore_odd

/-!
# CORE2A: the elementary API of Bender's notation

Everything in this file is proved, and everything is about the vocabulary of
`Submission.Work.CORE2A.Defs` (namespace `Work.GW2`):

* the conjugation helper `conjSub`, the inversion predicate `Inverts`, the sets
  `invSet`, `involutionSet`, and the predicates `OneInvClassIn`, `IsHallIn`;
* Bender's relation `BRel` and the subgroups `thompsonJ`, `ZJ` used by Lemma 2.4;
* the structural facts about `BenderSetup G` that Bender uses without comment
  (`S ≤ C_G(t)`, `|S| = 2|S₀|`, `Ĥ ≠ ⊤`, `U` odd, …), named `Work.CORE2A.bSetup_*`;
* the consequences of the configuration of Lemma 2.2 (`Lemma22Config`) and of the
  conclusion of Theorem 2.6 (`Thm26Concl`) that the later CORE areas need.

The definitions they speak about live in `Work.GW2` (`Submission.Work.CORE2A.Defs`);
the API lemmas live in `Work.CORE2A`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. A cyclic group has at most one element of order two -/

theorem eq_of_orderOf_eq_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- The involution of a cyclic group of even order is unique. -/
theorem eq_of_sq_eq_one_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  refine eq_of_orderOf_eq_two_of_isCyclic (a := a) (b := b) ?_ ?_
  · rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    exact ⟨ha, by rintro (h | h) <;> simp_all⟩
  · rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    exact ⟨hb, by rintro (h | h) <;> simp_all⟩

/-! ## 2. Conjugation of subgroups -/

section Conj

variable {G : Type*} [Group G]

theorem conjSub_eq_map (g : G) (K : Subgroup G) :
    conjSub g K = K.map (MulAut.conj g).toMonoidHom := rfl

theorem mem_conjSub_iff {g : G} {K : Subgroup G} {x : G} :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  rw [conjSub_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ * ((MulAut.conj g) y) * g ∈ K
    rw [MulAut.conj_apply]
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [this]
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- The same statement with `g` replaced by `g⁻¹`. -/
theorem mem_conjSub_iff' {g : G} {K : Subgroup G} {x : G} :
    x ∈ conjSub g⁻¹ K ↔ g * x * g⁻¹ ∈ K := by
  rw [mem_conjSub_iff]
  simp

theorem conjSub_mono {K L : Subgroup G} (h : K ≤ L) (g : G) : conjSub g K ≤ conjSub g L :=
  Subgroup.map_mono h

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem conjSub_sup (g : G) (K L : Subgroup G) : conjSub g (K ⊔ L) = conjSub g K ⊔ conjSub g L :=
  Subgroup.map_sup K L _

theorem conjSub_inf (g : G) (K L : Subgroup G) : conjSub g (K ⊓ L) = conjSub g K ⊓ conjSub g L :=
  Subgroup.map_inf K L _ (MulAut.conj g).injective

theorem card_conjSub (g : G) (K : Subgroup G) : Nat.card (conjSub g K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) :=
  Subgroup.map_injective (MulAut.conj g).injective

theorem comap_conj_eq_conjSub (g : G) (L : Subgroup G) :
    L.comap (MulAut.conj g).toMonoidHom = conjSub g⁻¹ L := by
  ext x
  rw [Subgroup.mem_comap, mem_conjSub_iff]
  simp

theorem conjSub_inv_conjSub (g : G) (K : Subgroup G) : conjSub g⁻¹ (conjSub g K) = K := by
  simp only [conjSub_eq_map, Subgroup.map_map]
  have hfun : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    show (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hfun, Subgroup.map_id]

theorem conjSub_conjSub_inv (g : G) (K : Subgroup G) : conjSub g (conjSub g⁻¹ K) = K := by
  simp only [conjSub_eq_map, Subgroup.map_map]
  have hfun : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    show (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hfun, Subgroup.map_id]

theorem conjSub_map_conjSub (g : G) (K : Subgroup G) :
    conjSub g (K.map (MulAut.conj g⁻¹).toMonoidHom) = K := conjSub_conjSub_inv g K

theorem conjSub_le_conjSub_iff {g : G} {K L : Subgroup G} :
    conjSub g K ≤ conjSub g L ↔ K ≤ L := by
  constructor
  · intro h x hx
    have h' : conjSub g⁻¹ (conjSub g K) ≤ conjSub g⁻¹ (conjSub g L) := conjSub_mono h g⁻¹
    have hK : conjSub g⁻¹ (conjSub g K) = K := conjSub_inv_conjSub g K
    have hL : conjSub g⁻¹ (conjSub g L) = L := conjSub_inv_conjSub g L
    rw [hK, hL] at h'
    exact h' hx
  · intro h
    exact conjSub_mono h g

theorem conjSub_le_iff {g : G} {K L : Subgroup G} : conjSub g K ≤ L ↔ K ≤ conjSub g⁻¹ L := by
  rw [conjSub_eq_map, Subgroup.map_le_iff_le_comap, comap_conj_eq_conjSub]

end Conj

/-! ## 3. `Inverts`, `invSet`, `involutionSet` -/

section Inverts

variable {G : Type*} [Group G]

theorem inverts_conjSub_le {s : G} {K : Subgroup G} (h : Inverts s K) : conjSub s K ≤ K := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : s * (s⁻¹ * x * s) * s⁻¹ = (s⁻¹ * x * s)⁻¹ := h _ hx
  have h2 : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rw [h1] at h2
  rw [← h2]
  exact inv_mem hx

theorem inverts_symm {s : G} {K : Subgroup G} (h : Inverts s K) : Inverts s⁻¹ K := by
  intro x hx
  have h1 : s * x⁻¹ * s⁻¹ = x := by
    have h1' := h x⁻¹ (inv_mem hx)
    rwa [inv_inv] at h1'
  have h3 : s⁻¹ * (s * x⁻¹ * s⁻¹) * s⁻¹⁻¹ = s⁻¹ * x * s⁻¹⁻¹ := by rw [h1]
  rw [← h3]
  group

theorem inverts_normalizes {s : G} {K : Subgroup G} (h : Inverts s K) (hs : s * s = 1) :
    s ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := h x hx
    rw [h1]
    exact inv_mem hx
  · intro hx
    have h3 : s * (s * x * s⁻¹) * s⁻¹ = (s * x * s⁻¹)⁻¹ := h _ hx
    have hssi : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs, inv_one]
    have hxeq : s * (s * x * s⁻¹) * s⁻¹ = x := by
      calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * (x * (s⁻¹ * s⁻¹)) := by group
        _ = x := by rw [hs, hssi, mul_one, one_mul]
    rw [← hxeq, h3]
    exact inv_mem hx

theorem inverts_sq_eq_one_of_mem_centralizer {s : G} {K : Subgroup G} (h : Inverts s K)
    {x : G} (hx : x ∈ K) (hxc : x ∈ centralizer ({s} : Set G)) : x ^ 2 = 1 := by
  have h1 : s * x * s⁻¹ = x⁻¹ := h x hx
  have h2 : s * x * s⁻¹ = x := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) s (by simp)
    rw [hcomm]
    group
  have h3 : x⁻¹ = x := by rw [← h1, h2]
  have h4 : x * x⁻¹ = 1 := mul_inv_cancel x
  rw [h3] at h4
  simpa [pow_two] using h4

theorem inverts_inf_centralizer_eq_bot_of_odd {s : G} {K : Subgroup G} (h : Inverts s K)
    (hodd : Odd (Nat.card K)) : K ⊓ centralizer ({s} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxK, hxc⟩
  have h2 : x ^ 2 = 1 := inverts_sq_eq_one_of_mem_centralizer h hxK hxc
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hdvdK : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvdK
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvdK)

theorem invSet_subset {G : Type*} [Group G] (K : Subgroup G) (s : G) : invSet K s ⊆ K :=
  fun _ hx => hx.1

theorem mem_invSet {G : Type*} [Group G] {K : Subgroup G} {s x : G} :
    x ∈ invSet K s ↔ x ∈ K ∧ s * x * s⁻¹ = x⁻¹ := Iff.rfl

theorem invSet_bot {G : Type*} [Group G] (s : G) :
    invSet (⊥ : Subgroup G) s = (⊥ : Subgroup G) := by
  ext x
  constructor
  · intro hx
    have hx1 : x = 1 := by simpa using hx.1
    rw [hx1]
    simp
  · intro hx
    have hx1 : x = 1 := by simpa using hx
    rw [hx1]
    exact ⟨by simp, by simp⟩

theorem one_mem_invSet {G : Type*} [Group G] {K : Subgroup G} {s : G} (h : (1 : G) ∈ K) :
    (1 : G) ∈ invSet K s := ⟨h, by simp⟩

theorem mem_involutionSet {G : Type*} [Group G] {K : Subgroup G} {x : G} :
    x ∈ involutionSet K ↔ x ∈ K ∧ orderOf x = 2 := Iff.rfl

theorem involutionSet_mono {G : Type*} [Group G] {K L : Subgroup G} (h : K ≤ L) :
    involutionSet K ⊆ involutionSet L := fun _ hx => ⟨h hx.1, hx.2⟩

end Inverts

/-! ## 4. `IsHallIn`, `IsFourGroup`, `BRel`, `ZJ` -/

section Misc

variable {G : Type*} [Group G]

theorem isHallIn_le {I K : Subgroup G} (h : IsHallIn I K) : I ≤ K := h.1

theorem isHallIn_coprime {I K : Subgroup G} (h : IsHallIn I K) :
    Nat.Coprime (Nat.card I) (I.relIndex K) := h.2

theorem isHallIn_bot (K : Subgroup G) : IsHallIn ⊥ K := by
  refine ⟨bot_le, ?_⟩
  simp [Subgroup.relIndex]

theorem isHallIn_self (K : Subgroup G) : IsHallIn K K := by
  refine ⟨le_rfl, ?_⟩
  simp [Subgroup.relIndex]

theorem IsFourGroup.card_eq {G : Type*} [Group G] {V : Subgroup G} (h : IsFourGroup V) :
    Nat.card V = 4 := h.1

theorem IsFourGroup.sq_eq_one' {G : Type*} [Group G] {V : Subgroup G} (h : IsFourGroup V)
    {v : G} (hv : v ∈ V) : v ^ 2 = 1 := h.2 v hv

theorem IsFourGroup.isMulCommutative' {G : Type*} [Group G] {V : Subgroup G}
    (h : IsFourGroup V) : IsMulCommutative V := by
  refine IsMulCommutative.of_comm fun x y => ?_
  have hx : x ^ 2 = 1 := Subtype.ext (by have := h.2 x.1 x.2; simpa using this)
  have hy : y ^ 2 = 1 := Subtype.ext (by have := h.2 y.1 y.2; simpa using this)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy)
  have hxy : (x * y) ^ 2 = 1 :=
    Subtype.ext (by have := h.2 (x * y).1 (x * y).2; simpa using this)
  have h1 : x * y = (x * y)⁻¹ := by
    have h2 : (x * y) * (x * y) = 1 := by simpa [pow_two] using hxy
    exact (inv_eq_of_mul_eq_one_left h2).symm
  rw [h1]
  show (x * y)⁻¹ = y * x
  rw [mul_inv_rev, hx', hy']

theorem bRel_refl {G : Type*} [Group G] (A : Subgroup G) : BRel A A :=
  ⟨⊥, bot_le, by
    rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G), top_inf_eq]
    exact Subgroup.map_subtype_le _⟩

theorem bRel_mono {G : Type*} [Group G] {A B B' : Subgroup G} (h : BRel A B) (hBB' : B ≤ B') :
    BRel A B' := by
  obtain ⟨X, hX, hXB⟩ := h
  exact ⟨X, hX, le_trans hXB hBB'⟩

theorem bRel_top {G : Type*} [Group G] (A : Subgroup G) : BRel A ⊤ :=
  bRel_mono (bRel_refl A) le_top

theorem mem_ZJ {G : Type*} [Group G] {P : Subgroup G} {x : G} :
    x ∈ ZJ P ↔ x ∈ thompsonJ P ∧ ∀ y ∈ thompsonJ P, y * x = x * y := by
  rw [ZJ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h; exact ⟨h.1, h.2⟩
  · intro h; exact ⟨h.1, h.2⟩

end Misc

/-! ## 5. The structural facts about `BenderSetup` (Bender p. 219) -/

section BenderSetupAPI

variable {G : Type} [Group G] [Finite G]

theorem bSetup_S0_normal (B : Work.GW2.BenderSetup G) :
    (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
  refine Subgroup.normal_of_index_eq_two ?_
  simpa [Subgroup.relIndex] using B.S0_index

theorem bSetup_card_S_eq (B : Work.GW2.BenderSetup G) :
    Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := by
  have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
  rw [inf_eq_left.mpr B.S0_le, B.S0_index] at h
  exact h.symm

theorem bSetup_S0_ne_S (B : Work.GW2.BenderSetup G) : B.S0 ≠ (B.S : Subgroup G) := by
  intro h
  have h2 : (2 : ℕ) = 1 := by
    have h3 := B.S0_index
    rw [h] at h3
    simpa [Subgroup.relIndex] using h3
  exact absurd h2 (by norm_num)

theorem bSetup_exists_mem_S_not_mem_S0 (B : Work.GW2.BenderSetup G) :
    ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 := by
  by_contra h
  have hle : (B.S : Subgroup G) ≤ B.S0 := fun x hx => by
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  exact bSetup_S0_ne_S B (le_antisymm B.S0_le hle)

theorem bSetup_t_mem_S (B : Work.GW2.BenderSetup G) : B.t ∈ (B.S : Subgroup G) :=
  B.S0_le B.t_mem

theorem bSetup_H_eq (B : Work.GW2.BenderSetup G) :
    B.H = centralizer ({B.t} : Set G) := rfl

theorem bSetup_U_eq (B : Work.GW2.BenderSetup G) : B.U = oddCoreIn B.H := rfl

theorem bSetup_t_mem_H (B : Work.GW2.BenderSetup G) : B.t ∈ B.H :=
  Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl

theorem bSetup_t_ne_one (B : Work.GW2.BenderSetup G) : B.t ≠ 1 := by
  intro h
  have ht := B.t_order
  rw [h, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem bSetup_Hhat_ne_top (B : Work.GW2.BenderSetup G) : B.Hhat ≠ ⊤ :=
  B.Hhat_coatom.ne_top

theorem bSetup_U_le_H (B : Work.GW2.BenderSetup G) : B.U ≤ B.H :=
  Subgroup.map_subtype_le _

theorem bSetup_U_le_Hhat (B : Work.GW2.BenderSetup G) : B.U ≤ B.Hhat :=
  le_trans (bSetup_U_le_H B) B.H_le_Hhat

theorem bSetup_t_mem_Hhat (B : Work.GW2.BenderSetup G) : B.t ∈ B.Hhat :=
  B.H_le_Hhat (bSetup_t_mem_H B)

theorem bSetup_Hhat_ne_bot (B : Work.GW2.BenderSetup G) : B.Hhat ≠ ⊥ := by
  intro h
  have ht := bSetup_t_mem_Hhat B
  rw [h] at ht
  exact bSetup_t_ne_one B (by simpa using ht)

theorem bSetup_U_odd (B : Work.GW2.BenderSetup G) : Odd (Nat.card B.U) := by
  have h := Work.ASM.oddCore_odd ↥B.H
  have hcard : Nat.card B.U = Nat.card (oddCore ↥B.H) := by
    show Nat.card ((oddCore ↥B.H).map (Subgroup.subtype _)) = Nat.card (oddCore ↥B.H)
    exact Subgroup.card_map_of_injective (Subtype.val_injective)
  rw [hcard]
  exact h

/-- **Bender p. 219**: `S ≤ C_G(t) = H`.  The involution `t` of the cyclic subgroup `S₀` is
central in `S`, because `S/S₀` acts on the cyclic group `S₀` and a cyclic group has a unique
element of order two. -/
theorem bSetup_S_le_H (B : Work.GW2.BenderSetup G) : (B.S : Subgroup G) ≤ B.H := by
  intro x hxS
  rw [show B.H = centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  by_cases hx0 : x ∈ B.S0
  · haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have h := mul_comm' (⟨B.t, B.t_mem⟩ : ↥B.S0) ⟨x, hx0⟩
    exact congrArg Subtype.val h
  · have hconj : x * B.t * x⁻¹ ∈ B.S0 := by
      have hN := bSetup_S0_normal B
      have hxT : x * B.t * x⁻¹ ∈ (B.S : Subgroup G) :=
        (B.S : Subgroup G).mul_mem
          ((B.S : Subgroup G).mul_mem hxS (B.S0_le B.t_mem)) (inv_mem hxS)
      have hmem : (⟨x * B.t * x⁻¹, hxT⟩ : ↥(B.S : Subgroup G)) ∈
          B.S0.subgroupOf (B.S : Subgroup G) := by
        have hcm := hN.conj_mem (⟨B.t, B.S0_le B.t_mem⟩ : ↥(B.S : Subgroup G))
          (by rw [Subgroup.mem_subgroupOf]; exact B.t_mem) (⟨x, hxS⟩ : ↥(B.S : Subgroup G))
        rw [Subgroup.mem_subgroupOf] at hcm
        exact hcm
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hord : orderOf (x * B.t * x⁻¹) = 2 := by
      have hsemi : SemiconjBy x B.t (x * B.t * x⁻¹) := by
        simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq x hsemi).symm.trans B.t_order
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have heq : (⟨x * B.t * x⁻¹, hconj⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic (a := (⟨x * B.t * x⁻¹, hconj⟩ : ↥B.S0))
        (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    have hval : x * B.t * x⁻¹ = B.t := congrArg Subtype.val heq
    have hx1 : x * B.t = B.t * x := by
      have h2 : (x * B.t * x⁻¹) * x = B.t * x := by rw [hval]
      simpa [mul_assoc] using h2
    exact hx1.symm

theorem bSetup_S_le_Hhat (B : Work.GW2.BenderSetup G) : (B.S : Subgroup G) ≤ B.Hhat :=
  le_trans (bSetup_S_le_H B) B.H_le_Hhat

end BenderSetupAPI

/-! ## 6. The configuration of Lemma 2.2 and the conclusion of Theorem 2.6 -/

section Config

variable {G : Type} [Group G] [Finite G]

theorem lemma22Prop_iff :
    Lemma22Prop ↔ ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, ¬ Lemma22Config B := Iff.rfl

theorem thm26Prop_iff :
    Thm26Prop ↔ ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Thm26Concl B := Iff.rfl

theorem lemma22Config_S0_le_centralizer {B : Work.GW2.BenderSetup G} (h : Lemma22Config B) :
    B.S0 ≤ centralizer (B.U : Set G) := h.1

theorem lemma22Config_exists_normal_invSet {B : Work.GW2.BenderSetup G}
    (h : Lemma22Config B) :
    ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 ∧
      ∃ I : Subgroup G, (I : Set G) = invSet B.U s ∧ (I.subgroupOf B.U).Normal ∧
        ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I → normalizer (X : Set G) ≤ B.H := h.2

theorem lemma22Config_of_U_eq_bot {B : Work.GW2.BenderSetup G} (hU : B.U = ⊥) :
    Lemma22Config B := by
  obtain ⟨s, hsS, hs0⟩ := bSetup_exists_mem_S_not_mem_S0 B
  refine ⟨?_, s, hsS, hs0, ⊥, ?_, ?_, ?_⟩
  · rw [hU]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw1 : w = 1 := by simpa using hw
    rw [hw1]
    simp
  · rw [hU, invSet_bot]
  · rw [hU]
    infer_instance
  · intro X hX hXbot
    exact absurd (le_bot_iff.mp hXbot) hX

/-- **Bender, Lemma 2.2**: `U ≠ 1`. -/
theorem lemma22Prop_U_ne_bot (h : Lemma22Prop) (hFT : FeitThompsonProp) (hctx : BenderCtx G)
    (B : Work.GW2.BenderSetup G) : B.U ≠ ⊥ := fun hU =>
  (lemma22Prop_iff.mp h) G hFT hctx B (lemma22Config_of_U_eq_bot hU)

theorem thm26Concl_oddCore_eq {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    oddCoreIn B.Hhat = B.U := h.1

theorem thm26Concl_centralizer_eq {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    (B.S : Subgroup G) ⊓ centralizer (B.U : Set G) = pCoreIn 2 B.Hhat := h.2.1

theorem thm26Concl_U_le_Hhat {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    B.U ≤ B.Hhat := by
  rw [← h.1]
  exact Subgroup.map_subtype_le _

theorem thm26Concl_O2_le_S {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
  rw [← h.2.1]
  exact inf_le_left

theorem thm26Concl_O2_le_Hhat {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    pCoreIn 2 B.Hhat ≤ B.Hhat := by
  rw [← h.2.1]
  exact le_trans inf_le_left (bSetup_S_le_Hhat B)

theorem thm26Concl_isPGroup_O2 {B : Work.GW2.BenderSetup G} (h : Thm26Concl B) :
    IsPGroup 2 (pCoreIn 2 B.Hhat) :=
  B.S.isPGroup'.to_le (thm26Concl_O2_le_S h)

end Config

/-! ## 7. Counting involutions in cosets (Bender §3) -/

section Counting

variable {G : Type} [Group G] [Finite G]

theorem cosetInvCount_le (Hh : Subgroup G) (g : G) : cosetInvCount Hh g ≤ Nat.card Hh := by
  refine Nat.card_le_card_of_injective
    (fun x : {x : G // orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} => (⟨g⁻¹ * x.1, x.2.2⟩ : Hh)) ?_
  intro a b hab
  have h : g⁻¹ * a.1 = g⁻¹ * b.1 := congrArg Subtype.val hab
  exact Subtype.ext (mul_left_cancel h)

theorem bCount_le_index (Hh : Subgroup G) (n : ℕ) : bCount Hh n ≤ Hh.index := by
  rw [bCount, Subgroup.index]
  exact Set.ncard_le_card _

end Counting

end Work.CORE2A
