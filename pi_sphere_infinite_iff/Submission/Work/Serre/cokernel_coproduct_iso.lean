import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

/-- **Cokernels commute with coproducts** (general form).

For a category with coproducts of shape `ι` and cokernels, the cokernel of the coproduct of a
family of maps is canonically the coproduct of the cokernels: the inclusion of the `i`-th summand
turns `f i` into `Sigma.map f`, so the maps `cokernel (f i) ⟶ cokernel (Sigma.map f)` (universal
property of the cokernels, glued by the coproduct) and the map `cokernel (Sigma.map f) ⟶ ∐ i,
cokernel (f i)` (descended from the coproduct of the cokernel projections) are mutually inverse. -/
theorem cokernel_coproduct_iso_general {C : Type*} [Category* C] [HasZeroMorphisms C]
    {ι : Type*} [HasCoproductsOfShape ι C] [HasCokernels C]
    {K L : ι → C} (f : ∀ i, K i ⟶ L i) :
    Nonempty (cokernel (Limits.Sigma.map f) ≅ ∐ fun i => cokernel (f i)) := by
  let F : ι → C := fun i => cokernel (f i)
  -- the map `f i` followed by the `i`-th summand of the cokernel projection is zero
  have hm (i : ι) : f i ≫ Sigma.ι L i ≫ cokernel.π (Limits.Sigma.map f) = 0 := by
    rw [← Limits.Sigma.ι_map_assoc (p := f) i, cokernel.condition, comp_zero]
  -- the coproduct of the cokernel projections lands in the cokernel of the coproduct map
  let d : (∐ L) ⟶ (∐ F) := Sigma.desc (fun i => cokernel.π (f i) ≫ Sigma.ι F i)
  have hd : Limits.Sigma.map f ≫ d = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map (p := f) i, Category.assoc, Sigma.ι_desc _ i,
      ← Category.assoc, cokernel.condition, zero_comp, comp_zero]
  -- the two comparison maps
  let v : cokernel (Limits.Sigma.map f) ⟶ (∐ F) := cokernel.desc (Limits.Sigma.map f) d hd
  let u : (∐ F) ⟶ cokernel (Limits.Sigma.map f) :=
    Sigma.desc (fun i => cokernel.desc (f i) (Sigma.ι L i ≫ cokernel.π (Limits.Sigma.map f)) (hm i))
  have huv : u ≫ v = 𝟙 (∐ F) := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc _ i, Category.comp_id]
    apply (cancel_epi (cokernel.π (f i))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc, Sigma.ι_desc _ i]
  have hvu : v ≫ u = 𝟙 (cokernel (Limits.Sigma.map f)) := by
    apply (cancel_epi (cokernel.π (Limits.Sigma.map f))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.comp_id]
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc _ i, Category.assoc, Sigma.ι_desc _ i,
      cokernel.π_desc]
  exact ⟨{ hom := v, inv := u, hom_inv_id := hvu, inv_hom_id := huv }⟩

/-- **Cokernels commute with coproducts** in the category of chain complexes of `ℤ`-modules. -/
theorem cokernel_coproduct_iso {ι : Type} {K L : ι → ChainComplex (ModuleCat ℤ) ℕ}
    (f : ∀ i, K i ⟶ L i) :
    Nonempty (CategoryTheory.Limits.cokernel (CategoryTheory.Limits.Sigma.map f) ≅
      ∐ fun i => CategoryTheory.Limits.cokernel (f i)) :=
  cokernel_coproduct_iso_general f

end Work.Serre
