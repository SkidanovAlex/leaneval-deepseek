import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open CategoryTheory

namespace Commons.RepresentationTheory.TateCohomology

/-- The short complex `(G →₀ M) --d₁₀--> M --norm--> M` whose middle homology computes the
`(-1)`-st Tate cohomology of the representation `M` (see `negOneShortComplexIso`). -/
private noncomputable def negOneShortComplex {G : Type} [Group G] [Fintype G]
    (M : Rep ℤ G) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (groupHomology.d₁₀ M) M.norm.toModuleCatHom (Rep.comp_eq_zero M)

/-- The short complex of the Tate complex of `M` in degrees `-2`, `-1`, `0` is
`(G →₀ M) --d₁₀--> M --norm--> M`. -/
private noncomputable def negOneShortComplexIso {G : Type} [Group G] [Fintype G]
    (M : Rep ℤ G) :
    HomologicalComplex.sc' (tateComplex M) (-2) (-1) 0 ≅ negOneShortComplex M :=
  ShortComplex.isoMk (groupHomology.chainsIso₁ M) (groupHomology.chainsIso₀ M)
    (groupCohomology.cochainsIso₀ M) (by
      change (groupHomology.chainsIso₁ M).hom ≫ groupHomology.d₁₀ M =
        (groupHomology.inhomogeneousChains M).d 1 0 ≫ (groupHomology.chainsIso₀ M).hom
      exact groupHomology.comp_d₁₀_eq M) (by
      change (groupHomology.chainsIso₀ M).hom ≫ M.norm.toModuleCatHom =
        M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
      rw [Rep.tateNorm]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The `(-1)`-st Tate cohomology of `M` is the homology of the short complex `negOneShortComplex`
in its middle degree. -/
private noncomputable def negOneIso {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) :
    tateCohomology M (-1) ≅ (negOneShortComplex M).moduleCatLeftHomologyData.H :=
  (HomologicalComplex.homologyIsoSc' (tateComplex M) (-2) (-1) 0
      (ComplexShape.prev_eq' (c := ComplexShape.up ℤ) (by rfl : (ComplexShape.up ℤ).Rel (-2) (-1)))
      (ComplexShape.next_eq' (c := ComplexShape.up ℤ) (by rfl : (ComplexShape.up ℤ).Rel (-1) 0))) ≪≫
    (ShortComplex.homologyMapIso (negOneShortComplexIso M)) ≪≫
    (negOneShortComplex M).moduleCatHomologyIso

/-- **Tate cohomology in degree `-1`.** For a finite group `G` and a `ℤ[G]`-module `V`, the
`(-1)`-st Tate cohomology of `V` is the quotient of the kernel of the norm map
`N = ∑_{g ∈ G} ρ(g)` by the image of the augmentation ideal, i.e. by the span of the elements
`ρ(g) v - v`. -/
theorem tateCohomology_neg_one_iso {G V : Type} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℤ V] (ρ : Representation ℤ G V) :
    Nonempty (letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
        (LinearMap.ker (Representation.norm ρ)).module
      tateCohomology (Rep.of ρ) (-1) ≃ₗ[ℤ]
        (LinearMap.ker (Representation.norm ρ)) ⧸
          (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
            (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) := by
  let s := negOneShortComplex (Rep.of ρ)
  letI : Module ℤ ↥(LinearMap.ker s.g.hom) := (LinearMap.ker s.g.hom).module
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  have h2 : (ModuleCat.Hom.hom s.f).range = Representation.Coinvariants.ker (Rep.of ρ).ρ :=
    groupHomology.range_d₁₀_eq_coinvariantsKer (Rep.of ρ)
  have hR : LinearMap.range (ShortComplex.moduleCatToCycles s) =
      Submodule.comap (LinearMap.ker s.g.hom).subtype
        (Representation.Coinvariants.ker (Rep.of ρ).ρ) := by
    rw [ShortComplex.moduleCatToCycles]
    exact (LinearMap.range_codRestrict _ _ _).trans
      (congrArg (Submodule.comap (LinearMap.ker s.g.hom).subtype) h2)
  have e1 : tateCohomology (Rep.of ρ) (-1) ≃ₗ[ℤ]
      ↥(ShortComplex.moduleCatLeftHomologyData s).H := (negOneIso (Rep.of ρ)).toLinearEquiv
  have e2 : ↥(ShortComplex.moduleCatLeftHomologyData s).H ≃ₗ[ℤ]
      (↥(LinearMap.ker s.g.hom) ⧸
        Submodule.comap (LinearMap.ker s.g.hom).subtype
          (Representation.Coinvariants.ker (Rep.of ρ).ρ)) := by
    convert Submodule.quotEquivOfEq (M := ↥(LinearMap.ker s.g.hom))
      (p := LinearMap.range (ShortComplex.moduleCatToCycles s))
      (p' := Submodule.comap (LinearMap.ker s.g.hom).subtype
        (Representation.Coinvariants.ker (Rep.of ρ).ρ)) hR using 2
    all_goals first | rfl | exact Subsingleton.elim _ _
  exact ⟨e1.trans e2⟩

end Commons.RepresentationTheory.TateCohomology