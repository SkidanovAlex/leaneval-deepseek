/-
# `Work.NormalComplement.sec1_lemma3_struct_regular`

Peterfalvi I Ch. III §1 Lemma 3 (p. 175), the **regularity** clause, in the form the rest of
`NormalComplement` needs: for `1 ≠ X ≤ V = C_D(t)` with `N_K(X) ≠ 1`, the subgroup
`K₁ = N_K(X) = C_K(X)` is cyclic and acts **sharply transitively** by conjugation on the
involutions of `N_H(X) = H ⊓ N_G(X)`.

Unlike `Work.NormalComplement.sec1_lemma3_struct` this uses only `ChIIFourProp` (no
`FeitThompsonProp`, no `ModelFactsProp`): the two inputs are

* `ChIIFourProp` P3 (`Y = X`) clause (d): `N_K(X) = C_K(X)` is a cyclic subgroup `K₁ ≤ C_G(X)`;
* Ch. I §2 Prop. 1 (c) / Prop. 2 (b) (`Work.ThmF.Bender.cardKsetEqInv` and
  `Work.ThmF.Bender.Kset_conj_injective`) applied **inside** `N_G(X)`: `N_H(X)` is strongly
  embedded in `N_G(X)` by `ChIIFourProp` P1 (b) with `F = N_G(X)`, and `t ∈ N_G(X) ∖ N_H(X)`
  is an involution there.  The two-point stabiliser of `t` inside `N_G(X)` is `D ∩ N_G(X)`, so
  `Kset N_H(X) t` (computed in `N_G(X)`) is exactly `K₁`.

Hence `|K₁| = |Inv N_H(X)|`, while `k ↦ k u k⁻¹` is injective on `K₁ ⊆ Kset H t` by
Ch. I §2 Lemma 1; so the orbit map is a bijection onto `Inv N_H(X)`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.Models.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThreePoints.P3NeBot.p3_b_aux
import Submission.Work.ThreePoints.P3NeBot.map_subtype_twoPoint_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Auxiliary facts (transport of `Kset` and of `involutions` to a subgroup) -/

section Helpers

variable {G : Type*} [Group G]

/-- Passing `Kset` down to a subgroup: an element `z` of `↥F` lies in `Kset` of the trace of
`H` iff its image in `G` lies in `F` and in `Kset H t`. -/
lemma mem_Kset_subgroupOf_iff {F H : Subgroup G} (t : ↥F) (z : ↥F) :
    z ∈ Work.ThmF.Kset (H.subgroupOf F) t ↔
      (z : G) ∈ F ∧ (z : G) ∈ Work.ThmF.Kset H (t : G) := by
  rw [Work.ThmF.mem_Kset_iff, Work.ThmF.mem_Kset_iff, Work.Models.mem_twoPoint_iff,
    Work.Models.mem_twoPoint_iff]
  constructor
  · rintro ⟨⟨hzH, htzH⟩, hz⟩
    refine ⟨z.2, ⟨Subgroup.mem_subgroupOf.mp hzH, ?_⟩, ?_⟩
    · simpa using Subgroup.mem_subgroupOf.mp htzH
    · simpa using congrArg Subtype.val hz
  · rintro ⟨hzF, ⟨hzH, htzH⟩, hz⟩
    refine ⟨⟨Subgroup.mem_subgroupOf.mpr hzH, ?_⟩, Subtype.ext ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      simpa using htzH
    · simpa using hz

/-- The image of `Kset` of a trace of `H` under the subtype map is the trace of `F` on
`Kset H t`. -/
lemma image_Kset_subgroupOf {F H : Subgroup G} (t : ↥F) :
    (fun z : ↥F => (z : G)) '' Work.ThmF.Kset (H.subgroupOf F) t
      = (F : Set G) ∩ Work.ThmF.Kset H (t : G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_Kset_subgroupOf_iff t z).mp hz
  · rintro ⟨hyF, hyK⟩
    exact ⟨⟨y, hyF⟩, (mem_Kset_subgroupOf_iff t ⟨y, hyF⟩).mpr ⟨hyF, hyK⟩, rfl⟩

/-- Passing `involutions` down to a subgroup. -/
lemma mem_involutions_subgroupOf_iff {F H : Subgroup G} (z : ↥F) :
    z ∈ involutions ((H.subgroupOf F : Subgroup ↥F) : Set ↥F) ↔
      (z : G) ∈ H ∧ orderOf (z : G) = 2 := by
  have hmem : z ∈ ((H.subgroupOf F : Subgroup ↥F) : Set ↥F) ↔ (z : G) ∈ H :=
    Subgroup.mem_subgroupOf
  have hord : orderOf (z : G) = orderOf z := (Subgroup.orderOf_mk z.1 z.2).symm
  rw [Work.Models.mem_involutions_iff, hmem]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hord]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← hord]; exact h2⟩

/-- The image of the involutions of a trace of `H` under the subtype map. -/
lemma image_involutions_subgroupOf {F H : Subgroup G} :
    (fun z : ↥F => (z : G)) '' involutions ((H.subgroupOf F : Subgroup ↥F) : Set ↥F)
      = involutions ((H ⊓ F : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzH, hz2⟩ := (mem_involutions_subgroupOf_iff z).mp hz
    exact ⟨Subgroup.mem_inf.mpr ⟨hzH, z.2⟩, hz2⟩
  · rintro ⟨hy, hy2⟩
    obtain ⟨hyH, hyF⟩ := Subgroup.mem_inf.mp hy
    exact ⟨⟨y, hyF⟩, (mem_involutions_subgroupOf_iff ⟨y, hyF⟩).mpr ⟨hyH, hy2⟩, rfl⟩

end Helpers

theorem sec1_lemma3_struct_regular (hC4 : Submission.Blueprint.ChIIFourProp)
    {G : Type} [Group G] [Finite G] (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Work.NormalComplement.Design.NK H t X, k ≠ 1) :
    ∃ K₁ : Subgroup G,
      (K₁ : Set G) = Work.NormalComplement.Design.NK H t X ∧
      Work.NormalComplement.Design.NK H t X = Work.NormalComplement.Design.CK H t X ∧
      IsCyclic ↥K₁ ∧
      (∀ u ∈ Submission.Blueprint.involutions
          ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
        ∀ v ∈ Submission.Blueprint.involutions
          ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
          ∃! k : G, k ∈ K₁ ∧ k * u * k⁻¹ = v) := by
  classical
  -- ## 0. standard abbreviations
  set NX : Subgroup G := Subgroup.normalizer (X : Set G) with hNXdef
  set M : Subgroup G := H ⊓ NX with hMdef
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- `t` centralises (hence normalises) `X`
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hXV hx)).2) t
      (Set.mem_singleton t)).symm
  have htNX : t ∈ NX := Subgroup.centralizer_le_normalizer (X : Set G) htC
  -- ## 1. the involution `u` of Ch. II §4 Prop. 2 (a)
  obtain ⟨u, huInv, huV⟩ := (hC4 G hS H hH t ht htH).2.1
  have huH : u ∈ H := huInv.1
  have hu2 : orderOf u = 2 := huInv.2
  have huC : u ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxV := hXV hx
    rw [huV] at hxV
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxV).2) u
      (Set.mem_singleton u)).symm
  have huNX : u ∈ NX := Subgroup.centralizer_le_normalizer (X : Set G) huC
  -- ## 2. `ChIIFourProp` P3 (case `Y = X`): `K₁ = N_K(X) = C_K(X)` is a cyclic subgroup
  obtain ⟨k₀, hk₀, hk₀ne⟩ := hNK
  have hNK' : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := ⟨k₀, hk₀.1, hk₀ne, hk₀.2⟩
  have hP3 := (hC4 G hS H hH t ht htH).2.2.2.1 X hX hXV hNK'
  dsimp only at hP3
  obtain ⟨-, -, -, ⟨K₁, hK₁car, hK₁C, hK₁cyc⟩⟩ := hP3
  -- ## 3. the two descriptions of `K₁` as a set
  have hK₁car' : (K₁ : Set G) = Work.ThmF.Kset H t ∩ (NX : Set G) := by
    rw [hNXdef]
    exact hK₁car
  have hK₁NK : (K₁ : Set G) = Work.NormalComplement.Design.NK H t X := by
    rw [Work.NormalComplement.Design.NK, ← hNXdef]
    exact hK₁car
  -- ## 4. `N_K(X) = C_K(X)`
  have hNKsubsetC : Work.NormalComplement.Design.NK H t X ⊆
      (Subgroup.centralizer (X : Set G) : Set G) := by
    rw [← hK₁NK]
    exact fun k hk => hK₁C hk
  have hNKeqCK : Work.NormalComplement.Design.NK H t X =
      Work.NormalComplement.Design.CK H t X := by
    rw [Work.NormalComplement.Design.CK]
    refine le_antisymm ?_ ?_
    · intro x hx
      exact ⟨hx.1, hNKsubsetC hx⟩
    · intro x hx
      exact ⟨hx.1, Subgroup.centralizer_le_normalizer (X : Set G) hx.2⟩
  -- ## 5. `N_H(X)` is strongly embedded in `N_G(X)` (`ChIIFourProp` P1 (b) with `F = N_G(X)`)
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hXV
  have hInvSub : Submission.Blueprint.involutions
      (Subgroup.centralizer (X : Set G) : Set G) ⊆ (NX : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer (X : Set G) hy.1
  have hXH : X ≤ Submission.Blueprint.conj (1 : G) H := by
    rw [Work.Models.conj_one]
    exact hXV.trans (le_trans inf_le_left inf_le_left)
  have hSE0 : IsStronglyEmbedded ((NX ⊓ H).subgroupOf NX) := by
    have h0 := (hC4 G hS H hH t ht htH).1 X NX hX3 hInvSub (le_of_eq hNXdef) 1 hXH
    rw [Work.Models.conj_one] at h0
    exact h0
  -- ## 6. the same statement in terms of `M' = N_H(X)` inside `↥N_G(X)`
  set M' : Subgroup ↥NX := M.subgroupOf NX with hM'def
  set t' : ↥NX := ⟨t, htNX⟩ with ht'def
  have hM'eq : M' = (NX ⊓ H).subgroupOf NX := by
    ext z
    rw [hM'def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hMdef, Subgroup.mem_inf,
      Subgroup.mem_inf]
    tauto
  have hM'eqH : M' = H.subgroupOf NX := by
    ext z
    rw [hM'def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hMdef, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
  have hSE : IsStronglyEmbedded M' := by
    rw [hM'eq]
    exact hSE0
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, Subgroup.orderOf_mk]
    exact ht
  have ht'M : t' ∉ M' := by
    intro h
    rw [hM'eqH, Subgroup.mem_subgroupOf] at h
    rw [ht'def] at h
    exact htH h
  -- ## 7. Ch. I §2 Prop. 1 (c): `|Kset N_H(X) t| = |Inv N_H(X)|`
  have hcard := Work.ThmF.Bender.cardKsetEqInv hSE ht'2 ht'M
  -- ## 8. transport to `G`: `|Kset H t ∩ N_G(X)| = |Inv N_H(X)|`
  have hinjval : ∀ a b : ↥NX, (a : G) = (b : G) → a = b := fun _ _ h => Subtype.val_injective h
  have himgKset : (fun z : ↥NX => (z : G)) '' Work.ThmF.Kset M' t'
      = (NX : Set G) ∩ Work.ThmF.Kset H t := by
    rw [hM'eqH]
    simpa [ht'def] using image_Kset_subgroupOf (F := NX) (H := H) t'
  have himgInv : (fun z : ↥NX => (z : G)) '' Submission.Blueprint.involutions (M' : Set ↥NX)
      = Submission.Blueprint.involutions (M : Set G) := by
    rw [hM'eqH, image_involutions_subgroupOf (F := NX) (H := H)]
  have hcardNK : ((NX : Set G) ∩ Work.ThmF.Kset H t).ncard
      = (Submission.Blueprint.involutions (M : Set G)).ncard := by
    have h1 : (Work.ThmF.Kset M' t').ncard
        = ((NX : Set G) ∩ Work.ThmF.Kset H t).ncard := by
      rw [← himgKset]
      exact (Set.InjOn.ncard_image (f := fun z : ↥NX => (z : G))
        (fun a _ b _ h => hinjval a b h)).symm
    have h2 : (Submission.Blueprint.involutions (M' : Set ↥NX)).ncard
        = (Submission.Blueprint.involutions (M : Set G)).ncard := by
      rw [← himgInv]
      exact (Set.InjOn.ncard_image (f := fun z : ↥NX => (z : G))
        (fun a _ b _ h => hinjval a b h)).symm
    rw [← h1]
    exact hcard.trans h2
  have hcardK₁ : (K₁ : Set G).ncard
      = (Submission.Blueprint.involutions (M : Set G)).ncard := by
    rw [hK₁car', Set.inter_comm]
    exact hcardNK
  -- ## 9. sharp transitivity of `K₁` on the involutions of `N_H(X)`
  refine ⟨K₁, hK₁NK, hNKeqCK, hK₁cyc, ?_⟩
  intro u hu v hv
  obtain ⟨huM, hu2⟩ := hu
  obtain ⟨huH, huNX⟩ := Subgroup.mem_inf.mp huM
  have hf_mem : ∀ k ∈ (K₁ : Set G),
      k * u * k⁻¹ ∈ Submission.Blueprint.involutions (M : Set G) := by
    intro k hk
    have hkKset : k ∈ Work.ThmF.Kset H t := by
      rw [hK₁car'] at hk
      exact hk.1
    have hkNX : k ∈ NX := by
      rw [hK₁car'] at hk
      exact hk.2
    have hkH : k ∈ H := (Work.ThmF.Kset_subset H t hkKset).1
    exact ⟨Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hkH huH) (H.inv_mem hkH),
      NX.mul_mem (NX.mul_mem hkNX huNX) (NX.inv_mem hkNX)⟩,
      by rw [Work.ThmF.Bender.orderOf_conj_eq]; exact hu2⟩
  have hinj : Set.InjOn (fun k : G => k * u * k⁻¹) (K₁ : Set G) := by
    intro a ha b hb hab
    have hInj := Work.ThmF.Bender.Kset_conj_injective (H := H) hH ht htH huH hu2
    have haK : a ∈ Work.ThmF.Kset H t := by
      rw [hK₁car'] at ha
      exact ha.1
    have hbK : b ∈ Work.ThmF.Kset H t := by
      rw [hK₁car'] at hb
      exact hb.1
    exact hInj haK hbK hab
  have heq : (fun k : G => k * u * k⁻¹) '' (K₁ : Set G)
      = Submission.Blueprint.involutions (M : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hf_mem k hk
    · rw [Set.InjOn.ncard_image hinj]
      exact le_of_eq hcardK₁.symm
  have hv' : v ∈ (fun k : G => k * u * k⁻¹) '' (K₁ : Set G) := by
    rw [heq]
    exact hv
  obtain ⟨k, hk, hkv⟩ := hv'
  exact ⟨k, ⟨hk, hkv⟩, fun y hy => hinj hy.1 hk (hy.2.trans hkv.symm)⟩

end Work.NormalComplement
