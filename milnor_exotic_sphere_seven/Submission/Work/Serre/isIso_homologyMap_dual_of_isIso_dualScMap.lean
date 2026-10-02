import Mathlib
import Submission.Work.StemsB.FieldDualUCT

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From an isomorphism on homology in one degree of the dual complex to an isomorphism of the
corresponding homology map

For a field `F`, a chain map `φ : C ⟶ D` of `ℕ`-indexed chain complexes of `F`-modules and a degree
`k`, the cochain map `dualComplexMap F C D φ : dualComplex F D ⟶ dualComplex F C` is a map of
cochain complexes.  Its `k`-th cohomology map `homologyMap (dualComplexMap F C D φ) k` is, by
definition, computed as the map induced on the homology of the short complex
`(dualComplex F D).sc' (k-1) k (k+1) ⟶ (dualComplex F C).sc' (k-1) k (k+1)`.
The main result of this file shows that it is an isomorphism as soon as the map induced on the left
homology of that short complex (in the explicit `moduleCatLeftHomologyData` model) is.

The two ingredients are completely general:

* `leftHomologyMap'_isIso_homologyMap` : if the map induced on left homology of a morphism of short
  complexes is an isomorphism (for *any* chosen left homology data), then so is the induced map on
  homology;
* `homologyMap_isIso_of_iso_square` : `IsIso` of the homology map is invariant under replacing a
  morphism of short complexes by one fitting into a commutative square whose vertical maps are
  isomorphisms.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

section

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- If the map induced on left homology by a morphism `ψ` of short complexes is an isomorphism
(for arbitrary left homology data), then so is the induced map on homology. -/
theorem leftHomologyMap'_isIso_homologyMap {S₁ S₂ : ShortComplex C} (ψ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) [S₁.HasHomology] [S₂.HasHomology]
    (h : IsIso (ShortComplex.leftHomologyMap' ψ h₁ h₂)) :
    IsIso (ShortComplex.homologyMap ψ) := by
  rw [ShortComplex.LeftHomologyMapData.homologyMap_eq ψ (ShortComplex.leftHomologyMapData ψ h₁ h₂),
    ← ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq
      (ShortComplex.leftHomologyMapData ψ h₁ h₂)]
  infer_instance

/-- `IsIso` of the map induced on homology is invariant under perturbing a morphism of short
complexes along a commutative square whose vertical maps are isomorphisms. -/
theorem homologyMap_isIso_of_iso_square {S₁ S₂ S₁' S₂' : ShortComplex C} (ψ : S₁ ⟶ S₂)
    (ψ' : S₁' ⟶ S₂') (e₁ : S₁ ≅ S₁') (e₂ : S₂ ≅ S₂') (w : ψ ≫ e₂.hom = e₁.hom ≫ ψ')
    [S₁.HasHomology] [S₂.HasHomology] [S₁'.HasHomology] [S₂'.HasHomology]
    (h : IsIso (ShortComplex.homologyMap ψ')) : IsIso (ShortComplex.homologyMap ψ) := by
  have hψ : ψ = e₁.hom ≫ ψ' ≫ e₂.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hψ, ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp]
  infer_instance

end

theorem isIso_homologyMap_dual_of_isIso_dualScMap {F : Type} [Field F]
    {C D : ChainComplex (ModuleCat.{0,0} F) ℕ} (φ : C ⟶ D) (k : ℕ)
    (h : IsIso (ShortComplex.leftHomologyMap'
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) (ComplexShape.up ℕ)
        (k - 1) k (k + 1)).map (Work.Cohomology.dualComplexMap F C D φ))
      ((Work.Cohomology.dualComplex F D).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData
      ((Work.Cohomology.dualComplex F C).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData)) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D φ) k) := by
  -- The short complex `sc k` of the definition of `homologyMap` is the short complex at the
  -- indices `c.prev k`, `k`, `c.next k`, which are `k - 1` and `k + 1` for `c = up ℕ`.
  have hprev : (ComplexShape.up ℕ).prev k = k - 1 := by
    rcases k with _ | k
    · exact ComplexShape.prev_eq_self' _ _ (fun i (h : (ComplexShape.up ℕ).Rel i 0) =>
        Nat.succ_ne_zero i h)
    · exact ComplexShape.prev_eq' (ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)
  have hnext : (ComplexShape.up ℕ).next k = k + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)
  -- The two short complexes are canonically isomorphic, naturally in the complex.
  let e := HomologicalComplex.natIsoSc' (ModuleCat.{0,0} F) (ComplexShape.up ℕ) (k - 1) k (k + 1)
    hprev hnext
  have hψ' : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) (ComplexShape.up ℕ)
        (k - 1) k (k + 1)).map (Work.Cohomology.dualComplexMap F C D φ))) :=
    leftHomologyMap'_isIso_homologyMap _ _ _ h
  have hψ : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0,0} F) (ComplexShape.up ℕ) k).map
        (Work.Cohomology.dualComplexMap F C D φ))) :=
    homologyMap_isIso_of_iso_square _ _ (e.app (Work.Cohomology.dualComplex F D))
      (e.app (Work.Cohomology.dualComplex F C))
      (NatTrans.naturality e.hom (Work.Cohomology.dualComplexMap F C D φ)) hψ'
  exact hψ

end Work.Serre
