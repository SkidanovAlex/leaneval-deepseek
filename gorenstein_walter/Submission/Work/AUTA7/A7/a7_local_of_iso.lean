import Mathlib
import Submission.Work.AUTA7.Defs

namespace Work.AUTA7.A7

/-!
# Transporting the local structure of an involution centralizer across a group isomorphism

The contract `Work.GW2.A7InvolutionLocalProp` records the local structure of the centralizer of an
involution of `A₇`.  Here we show that this structure is *isomorphism invariant*: if `L` is any
finite group and `φ : L ≃* A₇` an isomorphism, then for any `z : L` of order `2` the structure
asked for by the contract holds in `L` as well.

The whole statement is transported along `φ`.  The two structural facts used are

* the image of a centralizer is the centralizer of the image
  (`centralizer_map_eq_of_inj_surj`), and
* the image of a normalizer is the normalizer of the image
  (`normalizer_map_eq_of_inj_surj`),

both for a bijective homomorphism; the remaining conjuncts (cardinality of `K`, normality of `K`
in the centralizer, `2`-subgroup bounds, absence of elements of order `4`) are transported by hand.
-/

section Centralizer

variable {G H : Type*} [Group G] [Group H]

/-- For a bijective homomorphism `f : G →* H`, the image of the centralizer of a set `s` is the
centralizer of the image of `s`. -/
theorem centralizer_map_eq_of_inj_surj (f : G →* H) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) (s : Set G) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro t ht
    obtain ⟨t', ht', rfl⟩ := ht
    rw [← map_mul, ← map_mul, hx t' ht']
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro t ht
    have h := hy (f t) ⟨t, ht, rfl⟩
    refine hinj ?_
    rw [map_mul, map_mul]
    exact h

/-- For a bijective homomorphism `f : G →* H`, the image of the normalizer of a subgroup `K` is the
normalizer of the image subgroup. -/
theorem normalizer_map_eq_of_inj_surj (f : G →* H) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) (K : Subgroup G) :
    (Subgroup.normalizer (K : Set G)).map f =
      Subgroup.normalizer ((K.map f : Subgroup H) : Set H) := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_set_normalizer_iff] at hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    rw [Subgroup.coe_map, Set.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨x * k * x⁻¹, (hx k).mp hk, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨m, hm, hmf⟩
      refine ⟨x⁻¹ * m * x, ?_, ?_⟩
      · refine (hx (x⁻¹ * m * x)).mpr ?_
        rw [show x * (x⁻¹ * m * x) * x⁻¹ = m from by group]
        exact hm
      · rw [map_mul, map_mul, map_inv, hmf]
        group
  · intro y hy
    rw [Subgroup.mem_set_normalizer_iff] at hy
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [Subgroup.coe_map] at hy
    have keyK : h ∈ (K : Set G) ↔ f h ∈ f '' (K : Set G) := by
      constructor
      · intro hh; exact ⟨h, hh, rfl⟩
      · rintro ⟨m, hm, hmf⟩; rwa [hinj hmf] at hm
    have key2 : (f x * f h * (f x)⁻¹ ∈ f '' (K : Set G)) ↔ (x * h * x⁻¹ ∈ (K : Set G)) := by
      have heq : f x * f h * (f x)⁻¹ = f (x * h * x⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [heq]
      constructor
      · rintro ⟨m, hm, hmf⟩; rwa [hinj hmf] at hm
      · intro hh; exact ⟨x * h * x⁻¹, hh, rfl⟩
    exact keyK.trans ((hy (f h)).trans key2)

end Centralizer

theorem a7_local_of_iso {L : Type*} [Group L] [Finite L]
    (hprop : Work.GW2.A7InvolutionLocalProp)
    (φ : L ≃* alternatingGroup (Fin 7)) (z : L) (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) = 24 ∧
    ∃ K : Subgroup L, K ≤ Subgroup.centralizer ({z} : Set L) ∧
      (K.subgroupOf (Subgroup.centralizer ({z} : Set L))).Normal ∧
      Nat.card K = 3 ∧
      Nat.card (Subgroup.centralizer (K : Set L)) = 36 ∧
      Nat.card (Subgroup.normalizer (K : Set L)) = 72 ∧
      (∀ P : Subgroup L, P ≤ Subgroup.centralizer (K : Set L) → IsPGroup 2 P →
        Nat.card P ≤ 4) ∧
      (∀ x ∈ Subgroup.centralizer (K : Set L), orderOf x ≠ 4) := by
  -- view the isomorphism as a bijective monoid homomorphism
  let f : L →* alternatingGroup (Fin 7) := (φ : L →* alternatingGroup (Fin 7))
  have hfinj : Function.Injective f := φ.injective
  have hfsurj : Function.Surjective f := φ.surjective
  have hz' : orderOf (f z) = 2 := by rw [orderOf_injective f hfinj, hz]
  obtain ⟨hc24, K', hle', hnorm', hcard3', hcK', hnK', hpg', hord'⟩ := hprop (f z) hz'
  -- `K` is the preimage of `K'` under `φ`.
  set K : Subgroup L := K'.comap f with hKdef
  have hKmap : K.map f = K' := Subgroup.map_comap_eq_self_of_surjective hfsurj K'
  have hcoe : f '' (K : Set L) = (K' : Set (alternatingGroup (Fin 7))) := by
    rw [← Subgroup.coe_map, hKmap]
  have hcen : (Subgroup.centralizer (K : Set L)).map f =
      Subgroup.centralizer (K' : Set (alternatingGroup (Fin 7))) := by
    rw [centralizer_map_eq_of_inj_surj f hfinj hfsurj (K : Set L), hcoe]
  have hnorm_eq : (Subgroup.normalizer (K : Set L)).map f =
      Subgroup.normalizer (K' : Set (alternatingGroup (Fin 7))) := by
    rw [normalizer_map_eq_of_inj_surj f hfinj hfsurj K, hKmap]
  refine ⟨?_, K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|C_L(z)| = 24`
    have hmap := centralizer_map_eq_of_inj_surj f hfinj hfsurj ({z} : Set L)
    rw [Set.image_singleton] at hmap
    calc Nat.card (Subgroup.centralizer ({z} : Set L))
        = Nat.card ((Subgroup.centralizer ({z} : Set L)).map f) :=
          (Subgroup.card_map_of_injective hfinj).symm
      _ = Nat.card (Subgroup.centralizer ({(f z)} : Set (alternatingGroup (Fin 7)))) := by
            rw [hmap]
      _ = 24 := hc24
  · -- `K ≤ C_L(z)`
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' : f x ∈ K' := Subgroup.mem_comap.mp hx
    have hcomm : f x * f z = f z * f x :=
      (Subgroup.mem_centralizer_singleton_iff).mp (hle' hx')
    refine hfinj ?_
    rw [map_mul, map_mul]
    exact hcomm
  · -- `K ◁ C_L(z)`
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_comap.mpr ?_
    have hn' : f (n : L) ∈ K' := Subgroup.mem_comap.mp hn
    have hg' : f (g : L) ∈ Subgroup.centralizer ({(f z)} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : (g : L) * z = z * (g : L) :=
        (Subgroup.mem_centralizer_singleton_iff).mp g.2
      simpa only [map_mul] using congrArg f h
    have hconj := (Subgroup.normal_subgroupOf_iff hle').mp hnorm' (f (n : L)) (f (g : L)) hn' hg'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hconj
  · -- `|K| = 3`
    have h1 : Nat.card (K.map f) = Nat.card K := Subgroup.card_map_of_injective hfinj
    rw [hKmap] at h1
    omega
  · -- `|C_L(K)| = 36`
    calc Nat.card (Subgroup.centralizer (K : Set L))
        = Nat.card ((Subgroup.centralizer (K : Set L)).map f) :=
          (Subgroup.card_map_of_injective hfinj).symm
      _ = Nat.card (Subgroup.centralizer (K' : Set (alternatingGroup (Fin 7)))) := by rw [hcen]
      _ = 36 := hcK'
  · -- `|N_L(K)| = 72`
    calc Nat.card (Subgroup.normalizer (K : Set L))
        = Nat.card ((Subgroup.normalizer (K : Set L)).map f) :=
          (Subgroup.card_map_of_injective hfinj).symm
      _ = Nat.card (Subgroup.normalizer (K' : Set (alternatingGroup (Fin 7)))) := by rw [hnorm_eq]
      _ = 72 := hnK'
  · -- every `2`-subgroup of `C_L(K)` has order at most `4`
    intro P hP hPg
    have hmapP : (P.map f : Subgroup (alternatingGroup (Fin 7))) ≤
        Subgroup.centralizer (K' : Set (alternatingGroup (Fin 7))) := by
      have h := Subgroup.map_mono (f := f) hP
      rw [hcen] at h
      exact h
    have hbound := hpg' (P.map f) hmapP (IsPGroup.map hPg f)
    rwa [Subgroup.card_map_of_injective hfinj] at hbound
  · -- no element of `C_L(K)` has order `4`
    intro x hx h4
    have hx' : f x ∈ Subgroup.centralizer (K' : Set (alternatingGroup (Fin 7))) := by
      have hmem : f x ∈ (Subgroup.centralizer (K : Set L)).map f := ⟨x, hx, rfl⟩
      rwa [hcen] at hmem
    exact hord' (f x) hx' (by rw [orderOf_injective f hfinj, h4])

end Work.AUTA7.A7
