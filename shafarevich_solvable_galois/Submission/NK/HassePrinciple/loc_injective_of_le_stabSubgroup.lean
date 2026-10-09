import Mathlib
import Submission.NK.BrauerHasse.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation at a place whose decomposition group contains `U` is injective

Let `U ≤ Gal(K'/K)` be a subgroup and `A` a place of `K'` over a finite prime of `K`, with
decomposition group `D_A = stabSubgroup A.1`.  This module proves that if `U ≤ D_A`, then the
localisation

`H2Profinite.loc p U · A : H²(U, Z/p) ⟶ LocalH2 p U A.1`

is injective.  In fact, the local and the global filtered systems coincide on the nose: for every
finite Galois intermediate field `L`, the local level group
`(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` is the global level group `U/(U ∩ Gal(K'/L))`, and the
level-wise localisation `locLevel p U A.1 L` is the map on `H²` induced by the isomorphism
`U ⊓ D_A ≅ U` (`Subgroup.inclusion inf_le_left`, bijective because `U ≤ D_A`); hence it is
injective.  The injectivity on the colimit follows from the level-wise description of equality in
the filtered colimits (`ofLevel_eq_iff`, `local_ofLevel_eq_iff`).

## Main results

* `NK.HassePrinciple.localInclHom_bijective_of_le_stabSubgroup` — the level groups coincide;
* `NK.HassePrinciple.locLevel_injective_of_le_stabSubgroup` — `locLevel` is injective;
* `NK.HassePrinciple.loc_injective_of_le_stabSubgroup` — the localisation itself is injective.
-/

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-! ## General auxiliary lemmas -/

/-- `H2.map` of a bijective group homomorphism is injective: the inverse homomorphism exhibits
`H2.map f` as a split monomorphism. -/
lemma h2Map_injective_of_bijective {p : ℕ} {G H : Type u} [Group G] [Group H] (f : G →* H)
    (hf : Function.Bijective f) : Function.Injective (H2.map (p := p) f) := by
  let e : H ≃* G := (MulEquiv.ofBijective f hf).symm
  have hcomp : H2.map (p := p) f ≫ H2.map (p := p) (e : H →* G) = 𝟙 (H2 p H) := by
    rw [← H2.map_comp]
    rw [← H2.map_id (p := p) (G := H)]
    congr 1
    ext x
    simp [e]
  intro x y hxy
  have key : ∀ z : H2 p H,
      (H2.map (p := p) (e : H →* G)).hom ((H2.map (p := p) f).hom z) = z := by
    intro z
    have h1 := congrArg (fun (k : H2 p H ⟶ H2 p H) => k.hom z) hcomp
    simpa [ModuleCat.comp_apply] using h1
  calc x = (H2.map (p := p) (e : H →* G)).hom ((H2.map (p := p) f).hom x) := (key x).symm
    _ = (H2.map (p := p) (e : H →* G)).hom ((H2.map (p := p) f).hom y) := by rw [hxy]
    _ = y := key y

/-- The map induced by a group homomorphism on quotients is injective when the source normal
subgroup is the full preimage of the target normal subgroup. -/
lemma quotientGroupMap_injective_of_comap_le {G H : Type u} [Group G] [Group H] (f : G →* H)
    (M : Subgroup H) [M.Normal] (N : Subgroup G) [N.Normal] (hN : N ≤ M.comap f)
    (hMN : M.comap f ≤ N) : Function.Injective (QuotientGroup.map N M f hN) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, Subgroup.map_eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff x).mpr (hMN hx)

/-- The map induced by a group homomorphism on quotients is surjective when the homomorphism
is. -/
lemma quotientGroupMap_surjective_of_surjective {G H : Type u} [Group G] [Group H] (f : G →* H)
    (M : Subgroup H) [M.Normal] (N : Subgroup G) [N.Normal] (hN : N ≤ M.comap f)
    (hf : Function.Surjective f) : Function.Surjective (QuotientGroup.map N M f hN) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨QuotientGroup.mk' N x, QuotientGroup.map_mk' N M f hN x⟩

/-- The map induced by a bijective group homomorphism on quotients, when the source normal
subgroup is the full preimage of the target normal subgroup, is bijective. -/
lemma quotientGroupMap_bijective_of_comap {G H : Type u} [Group G] [Group H] (f : G →* H)
    (M : Subgroup H) [M.Normal] (N : Subgroup G) [N.Normal] (hN : N ≤ M.comap f)
    (hMN : M.comap f ≤ N) (hf : Function.Bijective f) :
    Function.Bijective (QuotientGroup.map N M f hN) :=
  ⟨quotientGroupMap_injective_of_comap_le f M N hN hMN,
    quotientGroupMap_surjective_of_surjective f M N hN hf.2⟩

/-- For `U ≤ D` the inclusion `U ⊓ D →* U` is bijective (indeed the identity on the underlying
sets). -/
lemma subgroupInclusion_inf_left_bijective {G : Type u} [Group G] {U D : Subgroup G} (h : U ≤ D) :
    Function.Bijective (Subgroup.inclusion (inf_le_left : U ⊓ D ≤ U) : ↥(U ⊓ D) →* ↥U) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥U => (z : G)) hxy
  · intro y
    exact ⟨⟨y.1, y.2, h y.2⟩, Subtype.ext rfl⟩

/-! ## The local and global level systems coincide when `U ≤ D_A` -/

/-- If `U ≤ D_A`, then the inclusion of the local level group
`(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` into the global level group `U/(U ∩ Gal(K'/L))` is
bijective: the local and the global level systems coincide. -/
lemma localInclHom_bijective_of_le_stabSubgroup {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U : Subgroup Gal(K'/K)} (A : ValuationSubring K')
    (h : U ≤ stabSubgroup A) (L : FiniteGaloisIntermediateField K K') :
    Function.Bijective (localInclHom U A L) := by
  have hbij := subgroupInclusion_inf_left_bijective (U := U) (D := stabSubgroup A) h
  have hN : L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A) ≤
      (L.fixingSubgroup.subgroupOf U).comap
        (Subgroup.inclusion (inf_le_left : U ⊓ stabSubgroup A ≤ U)) := by
    rw [Subgroup.comap_inclusion_subgroupOf]
  have hMN : (L.fixingSubgroup.subgroupOf U).comap
        (Subgroup.inclusion (inf_le_left : U ⊓ stabSubgroup A ≤ U)) ≤
      L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A) := by
    rw [Subgroup.comap_inclusion_subgroupOf]
  have key := quotientGroupMap_bijective_of_comap
    (Subgroup.inclusion (inf_le_left : U ⊓ stabSubgroup A ≤ U)) (L.fixingSubgroup.subgroupOf U)
    (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A)) hN hMN hbij
  have heq : localInclHom U A L =
      QuotientGroup.map (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
        (L.fixingSubgroup.subgroupOf U)
        (Subgroup.inclusion (inf_le_left : U ⊓ stabSubgroup A ≤ U)) hN := by
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  rwa [heq]

/-- If `U ≤ D_A`, the level-wise localisation `locLevel p U A L` is injective, being the map
induced on `H²` by the bijection `localInclHom U A L`. -/
lemma locLevel_injective_of_le_stabSubgroup {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} (A : ValuationSubring K')
    (h : U ≤ stabSubgroup A) (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (locLevel p U A L) := by
  simpa only [locLevel] using
    h2Map_injective_of_bijective (p := p) (localInclHom U A L)
      (localInclHom_bijective_of_le_stabSubgroup A h L)

/-- **The localisation at a place containing `U` in its decomposition group is injective.**

If a closed subgroup `U ≤ Gal(K'/K)` is contained in the decomposition group `stabSubgroup A.1` of
a place `A` of `K'` over a finite prime of `K`, then the localisation `x ↦ H2Profinite.loc p U x A`
is injective on `H²(U, Z/p)`: such an "inert" place detects every nonzero class.  In fact the
filtered systems defining `H2Profinite p U` and `LocalH2 p U A.1` coincide (the local level groups
`(U ⊓ stabSubgroup A.1)/((U ⊓ stabSubgroup A.1) ⊓ Gal(K'/M))` are the global level groups
`U/(U ⊓ Gal(K'/M))` when `U ≤ stabSubgroup A.1`), so the localisation at `A` is an isomorphism and
not merely injective. -/
theorem loc_injective_of_le_stabSubgroup (p : ℕ) {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U : Subgroup Gal(K'/K)}
    (A : NK.BrauerHasse.OverFinitePrime K K') (h : U ≤ NK.BrauerHasse.stabSubgroup A.1) :
    Function.Injective (fun x : NK.BrauerHasse.H2Profinite p U =>
      NK.BrauerHasse.H2Profinite.loc p U x A) := by
  intro x y hxy
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective (p := p) (U := U) x
  obtain ⟨L', b, rfl⟩ := H2Profinite.ofLevel_surjective (p := p) (U := U) y
  simp only [] at hxy
  rw [H2Profinite.loc_ofLevel_apply, H2Profinite.loc_ofLevel_apply] at hxy
  obtain ⟨M, h₁, h₂, he⟩ := (local_ofLevel_eq_iff p (U := U) (A := A.1)
    ((locLevel p U A.1 L) a) ((locLevel p U A.1 L') b)).mp hxy
  rw [← levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h₁) a,
      ← levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h₂) b] at he
  refine (ofLevel_eq_iff (p := p) (U := U) (L := L) (L' := L') a b).mpr
    ⟨M, h₁, h₂, ?_⟩
  exact locLevel_injective_of_le_stabSubgroup (p := p) (A := A.1) h M he

end NK.HassePrinciple
