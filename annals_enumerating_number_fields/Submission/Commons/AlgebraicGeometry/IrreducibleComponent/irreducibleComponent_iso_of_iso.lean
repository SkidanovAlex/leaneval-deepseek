import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.Combinatorics.Quiver.ReflQuiver

open CategoryTheory _root_.AlgebraicGeometry

namespace Commons.AlgebraicGeometry.IrreducibleComponent


/-- A homeomorphism induces a bijection between the sets of irreducible components. -/
theorem image_irreducibleComponents_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Set.image (Set.image ⇑h) (irreducibleComponents X) = irreducibleComponents Y := by
  have hmem : ∀ {V : Set X}, V ∈ irreducibleComponents X → ⇑h '' V ∈ irreducibleComponents Y :=
    fun hV => image_mem_irreducibleComponents_of_isPreirreducible_fiber ⇑h h.continuous h.isOpenMap
      (fun x => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible) h.surjective hV
  have hmem' : ∀ {V : Set Y}, V ∈ irreducibleComponents Y →
      ⇑h.symm '' V ∈ irreducibleComponents X :=
    fun hV => image_mem_irreducibleComponents_of_isPreirreducible_fiber ⇑h.symm h.symm.continuous
      h.symm.isOpenMap
      (fun x => (Set.subsingleton_singleton.preimage h.symm.injective).isPreirreducible)
      h.symm.surjective hV
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨V, hV, rfl⟩
    exact hmem hV
  · intro W hW
    refine ⟨⇑h.symm '' W, hmem' hW, ?_⟩
    rw [Set.image_image]
    have : (fun x => h (h.symm x)) = id := funext fun x => h.apply_symm_apply x
    rw [this, Set.image_id]

/-- Two open immersions with the same range have the same kernel ideal sheaf. -/
theorem ker_eq_of_range_eq_of_isOpenImmersion {X Y Z : AlgebraicGeometry.Scheme}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : Set.range ⇑f = Set.range ⇑g) : Scheme.Hom.ker f = Scheme.Hom.ker g := by
  have hker : (IsOpenImmersion.isoOfRangeEq f g h).hom.ker = ⊥ :=
    Scheme.Hom.ker_eq_bot_of_isIso _
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac f g h, Scheme.Hom.ker_comp, hker,
    Scheme.IdealSheafData.map_bot]

/-- An isomorphism of Noetherian schemes induces isomorphisms between corresponding
irreducible components (with their `irreducibleComponent` subscheme structures). -/
theorem irreducibleComponent_iso_of_iso {X Y : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (e : X ≅ Y) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ∃ Z', ∃ hZ' : Z' ∈ irreducibleComponents Y,
      Nonempty (AlgebraicGeometry.Scheme.irreducibleComponent X Z hZ ≅
        AlgebraicGeometry.Scheme.irreducibleComponent Y Z' hZ') := by
  let h : X ≃ₜ Y := Scheme.homeoOfIso e
  have hcoe : ⇑h = ⇑e.hom := Scheme.coe_homeoOfIso e
  have hZ' : ⇑h '' Z ∈ irreducibleComponents Y :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber ⇑h h.continuous h.isOpenMap
      (fun x => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible) h.surjective hZ
  refine ⟨⇑h '' Z, hZ', ?_⟩
  have hopen : ⇑h '' (Scheme.irreducibleComponentOpen X Z : Set X) =
      (Scheme.irreducibleComponentOpen Y (⇑h '' Z) : Set Y) := by
    have h1 : (Scheme.irreducibleComponentOpen X Z : Set X) =
        (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := rfl
    have h2 : (Scheme.irreducibleComponentOpen Y (⇑h '' Z) : Set Y) =
        (⋃₀ (irreducibleComponents Y \ {⇑h '' Z}))ᶜ := rfl
    rw [h1, h2, h.image_compl, Set.image_sUnion]
    congr 1
    rw [Set.image_sdiff (Set.image_injective.mpr h.injective), Set.image_singleton,
      image_irreducibleComponents_of_homeomorph h]
  have hrang : Set.range ⇑((Scheme.irreducibleComponentOpen X Z).ι ≫ e.hom) =
      Set.range ⇑((Scheme.irreducibleComponentOpen Y (⇑h '' Z)).ι) := by
    rw [show ⇑((Scheme.irreducibleComponentOpen X Z).ι ≫ e.hom) =
        ⇑e.hom ∘ ⇑(Scheme.irreducibleComponentOpen X Z).ι from rfl, Set.range_comp,
      Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← hcoe]
    exact hopen
  have hker : ((Scheme.irreducibleComponentOpen X Z).ι ≫ e.hom).ker =
      ((Scheme.irreducibleComponentOpen Y (⇑h '' Z)).ι).ker :=
    ker_eq_of_range_eq_of_isOpenImmersion _ _ hrang
  have hker₁ : (Y.irreducibleComponentι (⇑h '' Z) hZ').ker =
      ((Scheme.irreducibleComponentOpen Y (⇑h '' Z)).ι).ker := by
    unfold Scheme.irreducibleComponentι Scheme.irreducibleComponent
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.irreducibleComponentIdeal_def]
  have hker₂ : (Scheme.irreducibleComponentι X Z hZ ≫ e.hom).ker =
      ((Scheme.irreducibleComponentOpen Y (⇑h '' Z)).ι).ker := by
    have hX : (Scheme.irreducibleComponentι X Z hZ).ker =
        ((Scheme.irreducibleComponentOpen X Z).ι).ker := by
      unfold Scheme.irreducibleComponentι Scheme.irreducibleComponent
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.irreducibleComponentIdeal_def]
    rw [Scheme.Hom.ker_comp, hX, ← Scheme.Hom.ker_comp]
    exact hker
  have hker' : (Y.irreducibleComponentι (⇑h '' Z) hZ').ker =
      (Scheme.irreducibleComponentι X Z hZ ≫ e.hom).ker := hker₁.trans hker₂.symm
  have : IsIso (IsClosedImmersion.lift (Y.irreducibleComponentι (⇑h '' Z) hZ')
      (Scheme.irreducibleComponentι X Z hZ ≫ e.hom) hker'.le) :=
    IsClosedImmersion.isIso_lift _ _ hker'
  exact ⟨asIso (IsClosedImmersion.lift (Y.irreducibleComponentι (⇑h '' Z) hZ')
    (Scheme.irreducibleComponentι X Z hZ ≫ e.hom) hker'.le)⟩

end Commons.AlgebraicGeometry.IrreducibleComponent