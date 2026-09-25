import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.BocksteinDefs

/-!
# The order of a finite group annihilates its integral homology in positive degrees

For a finite group `G` and `n ≥ 1`, every element of the group homology `H_n(G, ℤ)` (trivial
integral coefficients) is annihilated by the order `|G|`.

The proof is the classical transfer argument, formalised through the induced representation
`Ind_{1}^{G} ℤ`:

* `|G| · 𝟙` on the trivial representation `ℤ` factors as the norm map
  `ν : ℤ ⟶ Ind_{1}^{G} ℤ`, `1 ↦ ∑_g ⟦g ⊗ 1⟧` followed by the augmentation
  `ε : Ind_{1}^{G} ℤ ⟶ ℤ`, `⟦x ⊗ a⟧ ↦ ε(x) a`;
* `H_{n+1}(G, Ind_{1}^{G} ℤ) ≅ H_{n+1}(1, ℤ) = 0` for `n + 1 ≥ 1` (Shapiro's lemma);
* the homology functor is `ℤ`-linear in the representation morphism, so that the composite above
  acts as `|G|` on homology and therefore as zero.

## Main result

* `Work.Tower.Shafarevich.CFT.HnZ_natCard_smul_eq_zero`
-/

namespace Work.Tower.Shafarevich.CFT

open CategoryTheory groupHomology

noncomputable section

/-! ## 1. The homology functor is `ℤ`-linear in the representation morphism -/

/-- `homologyMap` is `ℤ`-linear in the chain map: `H_i(c • φ) = c • H_i(φ)`. -/
lemma homologyMap_zsmul {C : Type*} [Category C] [Preadditive C] {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex C cs} (c : ℤ) (φ : K ⟶ L) (i : ι) [K.HasHomology i]
    [L.HasHomology i] :
    HomologicalComplex.homologyMap (c • φ) i = c • HomologicalComplex.homologyMap φ i := by
  let h : (K ⟶ L) →+ (K.homology i ⟶ L.homology i) :=
    { toFun := fun φ => HomologicalComplex.homologyMap φ i
      map_zero' := HomologicalComplex.homologyMap_zero K L i
      map_add' := fun φ ψ => HomologicalComplex.homologyMap_add φ ψ i }
  exact h.map_zsmul c φ

variable {G : Type} [Group G] [Fintype G]

/-- The chain map induced by a scalar multiple of the identity representation morphism is the
scalar multiple of the induced chain map. -/
lemma chainsMap_zsmul_id {G : Type} [Group G] (A : Rep ℤ G) (c : ℤ) :
    chainsMap (MonoidHom.id G) (c • 𝟙 A) = c • chainsMap (MonoidHom.id G) (𝟙 A) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ConcreteCategory.hom_ext
  intro v
  simp only [ConcreteCategory.hom]
  rw [show ((c • chainsMap (MonoidHom.id G) (𝟙 A)).f i) =
      c • ((chainsMap (MonoidHom.id G) (𝟙 A)).f i) from rfl]
  rw [show ((c • ((chainsMap (MonoidHom.id G) (𝟙 A)).f i)).hom') =
      c • ((chainsMap (MonoidHom.id G) (𝟙 A)).f i).hom' from rfl]
  rw [chainsMap_id, HomologicalComplex.id_f]
  change (ModuleCat.Hom.hom ((chainsMap (MonoidHom.id G) (c • 𝟙 A)).f i)) v = c • v
  rw [chainsMap_id_f_hom_eq_mapRange, Rep.zsmul_hom]
  simp only [Finsupp.mapRange.linearMap_apply]
  rfl

/-- The map `H_n(G, A) → H_n(G, A)` induced by `c • 𝟙_A` is multiplication by `c`. -/
lemma map_zsmul_id {G : Type} [Group G] (A : Rep ℤ G) (c : ℤ) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) (c • 𝟙 A) n = c • 𝟙 (groupHomology A n) := by
  rw [show groupHomology.map (MonoidHom.id G) (c • 𝟙 A) n
      = HomologicalComplex.homologyMap (chainsMap (MonoidHom.id G) (c • 𝟙 A)) n from rfl]
  rw [chainsMap_zsmul_id, homologyMap_zsmul, chainsMap_id, HomologicalComplex.homologyMap_id]
  rfl

/-- Elementwise form of `map_zsmul_id`. -/
lemma map_zsmul_id_apply {G : Type} [Group G] (A : Rep ℤ G) (c : ℤ) (n : ℕ) (x : groupHomology A n) :
    (groupHomology.map (MonoidHom.id G) (c • 𝟙 A) n) x = c • x := by
  rw [map_zsmul_id (A := A) (c := c) (n := n)]
  change (ConcreteCategory.hom (c • 𝟙 (groupHomology A n))) x = c • x
  simp

/-! ## 2. The induced representation `Ind_{1}^{G} ℤ` -/

/-- The trivial `ℤ`-linear representation on `ℤ`. -/
abbrev Triv (G : Type) [Group G] : Rep ℤ G := Rep.trivial ℤ G ℤ

/-- The trivial `ℤ`-linear representation of the trivial subgroup on `ℤ`. -/
abbrev A0 (G : Type) [Group G] : Rep ℤ ↥(⊥ : Subgroup G) := Rep.trivial ℤ ↥(⊥ : Subgroup G) ℤ

/-- The induced representation `Ind_{1}^{G} ℤ`, the regular representation of `G`. -/
abbrev IndTriv (G : Type) [Group G] : Rep ℤ G := Rep.ind (⊥ : Subgroup G).subtype (A0 G)

/-- `H_{n+1}(G, Ind_{1}^{G} ℤ) = 0`: Shapiro's lemma identifies it with `H_{n+1}(1, ℤ)` and the
group `1` is trivial. -/
lemma isZero_groupHomology_indTriv {G : Type} [Group G] (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupHomology (IndTriv G) (n + 1)) := by
  classical
  exact CategoryTheory.Limits.IsZero.of_iso
    (isZero_groupHomology_succ_of_subsingleton (A0 G) n)
    (groupHomology.indIso (⊥ : Subgroup G) (A0 G) (n + 1))

/-- The norm map `ν : ℤ ⟶ Ind_{1}^{G} ℤ` of `G`-representations, sending `1` to `∑_g ⟦g ⊗ 1⟧`. -/
noncomputable def normHom : Triv G ⟶ IndTriv G :=
  Rep.ofHom ⟨∑ g : G, Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g, by
    intro h
    apply LinearMap.ext_ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Rep.trivial_ρ]
    simp only [LinearMap.id_coe, id_eq]
    rw [LinearMap.sum_apply]
    rw [map_sum]
    exact (Fintype.sum_bijective (fun x : G => x * h⁻¹) (Group.mulRight_bijective h⁻¹)
      (fun x => (Representation.ind (⊥ : Subgroup G).subtype (A0 G).ρ h)
        ((Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ x) 1))
      (fun x => (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ x) 1)
      (fun x => by rw [Representation.ind_mk])).symm⟩

/-- The augmentation `ε : Ind_{1}^{G} ℤ ⟶ ℤ` of `G`-representations, sending `⟦g ⊗ a⟧` to `a`. -/
noncomputable def augHom : IndTriv G ⟶ Triv G :=
  (Rep.indResHomEquiv (⊥ : Subgroup G).subtype (A0 G) (Triv G)).symm (𝟙 (A0 G))

/-- The augmentation takes the value `a` on `⟦g ⊗ a⟧`. -/
lemma augHom_IndV_mk {G : Type} [Group G] (g : G) (a : ℤ) :
    augHom (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g a) = a := by
  have hbase : augHom (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ 1 (1 : ℤ)) = 1 := by
    have h : (Rep.indResHomEquiv (⊥ : Subgroup G).subtype (A0 G) (Triv G)) augHom = 𝟙 (A0 G) :=
      LinearEquiv.apply_symm_apply _ _
    have h1 := congrArg
      (fun (f : A0 G ⟶ Rep.res (⊥ : Subgroup G).subtype (Triv G)) => f (1 : ℤ)) h
    rw [Rep.indResHomEquiv_apply] at h1
    exact h1
  have hone : ∀ x : G,
      augHom (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ x (1 : ℤ)) = 1 := by
    intro x
    have heq : (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ x (1 : ℤ)) =
        (IndTriv G).ρ x⁻¹
          (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ 1 (1 : ℤ)) := by
      rw [Representation.ind_mk]
      simp
    rw [heq, Rep.hom_comm_apply, Rep.trivial_ρ_apply]
    exact hbase
  have hsmul : augHom (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g a) =
      a • augHom (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g (1 : ℤ)) := by
    conv_lhs => rw [show a = a • (1 : ℤ) by simp]
    rw [map_smul, map_smul]
  rw [hsmul, hone g, smul_eq_mul, mul_one]

/-- The composite of the norm with the augmentation is multiplication by the order of `G`. -/
lemma normHom_comp_augHom :
    normHom ≫ augHom = (Fintype.card G : ℤ) • 𝟙 (Triv G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext_ring
  rw [Rep.hom_comp_toLinearMap, LinearMap.comp_apply]
  have h1 : normHom.hom.toLinearMap (1 : ℤ)
      = ∑ g : G, Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g (1 : ℤ) := by
    change (∑ g : G, Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g) (1 : ℤ)
      = ∑ g : G, Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g (1 : ℤ)
    rw [LinearMap.sum_apply]
  rw [h1, map_sum]
  have h2 : ∀ g : G, augHom.hom.toLinearMap
      (Representation.IndV.mk (⊥ : Subgroup G).subtype (A0 G).ρ g (1 : ℤ)) = 1 := by
    intro g
    rw [Representation.IntertwiningMap.toLinearMap_apply]
    exact augHom_IndV_mk g 1
  rw [Finset.sum_congr rfl fun g _ => h2 g]
  have h3 : (((Fintype.card G : ℤ) • 𝟙 (Triv G)).hom).toLinearMap (1 : ℤ) =
      (Fintype.card G : ℤ) := by
    rw [Rep.zsmul_hom, Rep.hom_id]
    change ((Fintype.card G : ℤ) •
      (Representation.IntertwiningMap.id (Triv G).ρ).toLinearMap) (1 : ℤ) = (Fintype.card G : ℤ)
    rw [Representation.IntertwiningMap.toLinearMap_id, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul, mul_one]
  rw [h3]
  simp [Finset.sum_const, Finset.card_univ]

/-! ## 3. The main result -/

theorem HnZ_natCard_smul_eq_zero (G : Type) [Group G] [Fintype G] (k : ℕ) (hk : 1 ≤ k)
    (x : Work.CFT.ClassFormation.HnZ G k) : (Fintype.card G : ℤ) • x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hzero : CategoryTheory.Limits.IsZero (groupHomology (IndTriv G) (m + 1)) :=
    isZero_groupHomology_indTriv (G := G) m
  have hnu : groupHomology.map (MonoidHom.id G) (normHom (G := G)) (m + 1) = 0 :=
    hzero.eq_of_tgt _ _
  have hcomp := groupHomology.map_id_comp (normHom (G := G)) (augHom (G := G)) (m + 1)
  calc (Fintype.card G : ℤ) • x
      = (groupHomology.map (MonoidHom.id G) ((Fintype.card G : ℤ) • 𝟙 (Triv G)) (m + 1)) x :=
        (map_zsmul_id_apply (Triv G) (Fintype.card G : ℤ) (m + 1) x).symm
    _ = (groupHomology.map (MonoidHom.id G)
          (normHom (G := G) ≫ augHom (G := G)) (m + 1)) x := by
        rw [normHom_comp_augHom]
    _ = (groupHomology.map (MonoidHom.id G) (augHom (G := G)) (m + 1))
          ((groupHomology.map (MonoidHom.id G) (normHom (G := G)) (m + 1)) x) := by
        rw [hcomp]
        rfl
    _ = 0 := by
        rw [hnu]
        simp

end

end Work.Tower.Shafarevich.CFT
