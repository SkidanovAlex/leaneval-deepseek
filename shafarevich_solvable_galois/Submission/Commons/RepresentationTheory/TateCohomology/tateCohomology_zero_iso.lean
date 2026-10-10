import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The zeroth Tate cohomology group of a `G`-module

For a finite group `G` and a `ℤ`-linear representation `ρ` of `G` on an additive
commutative group `V`, the zeroth Tate cohomology `Ĥ⁰(G, V)` is the quotient of the
invariants `V^G` by the image of the norm map `N = ∑_{g : G} ρ g`:

  `Ĥ⁰(G, V) ≅ V^G / N(V)`.

This is the degree-zero part of the standard two-periodic exact sequence relating
Tate cohomology, group cohomology and group homology.  In the formalisation below
`tateCohomology M 0` is by definition `H₀` of Mathlib's Tate complex, which is the
connect of the inhomogeneous chain and cochain complexes of `M` via the norm.  In
degree `0` the homology is therefore `ker (d⁰) / im (N)`, and the two identifications
`ker (d⁰) = V^G` and `im (N) = N(V)` are the usual low-degree computations for group
cohomology.
-/

namespace Commons.RepresentationTheory.TateCohomology

open CategoryTheory Limits Representation

variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℤ V]

/-- The three-term complex `V --N--> V --d₀₁--> (G → V)` exhibiting the part of the Tate
complex around degree `0`.  Its homology is `Ĥ⁰`. -/
private noncomputable def auxS0 (ρ : Representation ℤ G V) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (Rep.Hom.toModuleCatHom (Rep.of ρ).norm) (groupCohomology.d₀₁ (Rep.of ρ))
    (Rep.norm_comp_d_eq_zero (Rep.of ρ))

private lemma aux_ker_S0_g (ρ : Representation ℤ G V) :
    LinearMap.ker (auxS0 ρ).g.hom = ρ.invariants := by
  rw [show (auxS0 ρ).g = groupCohomology.d₀₁ (Rep.of ρ) from rfl]
  exact groupCohomology.d₀₁_ker_eq_invariants (Rep.of ρ)

/-- The kernel of `d₀₁` is the invariants; this is the corresponding additive equivalence. -/
private noncomputable def aux_eKer (ρ : Representation ℤ G V) :
    ↥(LinearMap.ker (auxS0 ρ).g.hom) ≃+ ↥(ρ.invariants) where
  toFun y := ⟨y.1, (aux_ker_S0_g ρ).le y.2⟩
  invFun x := ⟨x.1, (aux_ker_S0_g ρ).ge x.2⟩
  left_inv y := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' y z := Subtype.ext rfl

private lemma aux_moduleCatToCycles_val (ρ : Representation ℤ G V) (z : V) :
    ((auxS0 ρ).moduleCatToCycles z).1 = ρ.norm z := rfl

/-- Under the identification `ker d₀₁ = V^G`, the image of the norm map in `ker d₀₁`
becomes exactly `N(V) ⊆ V^G`. -/
private lemma aux_map_P_eq_Q (ρ : Representation ℤ G V) :
    letI : Module ℤ ↥(LinearMap.ker (auxS0 ρ).g.hom) := (LinearMap.ker (auxS0 ρ).g.hom).module
    letI : Module ℤ ↥(ρ.invariants) := (ρ.invariants).module
    ((LinearMap.range (auxS0 ρ).moduleCatToCycles).toAddSubgroup).map (aux_eKer ρ) =
      (((LinearMap.range ρ.norm).comap ρ.invariants.subtype).toAddSubgroup) := by
  letI : Module ℤ ↥(LinearMap.ker (auxS0 ρ).g.hom) := (LinearMap.ker (auxS0 ρ).g.hom).module
  letI : Module ℤ ↥(ρ.invariants) := (ρ.invariants).module
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, LinearMap.mem_range]
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    show ρ.norm z = ((aux_eKer ρ) y : V)
    rw [show ((aux_eKer ρ) y : V) = (y.1 : V) from rfl]
    exact (show (y.1 : V) = ρ.norm z from by rw [← hz]; rfl).symm
  · intro hx
    rw [AddSubgroup.mem_map]
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, LinearMap.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨⟨x.1, (aux_ker_S0_g ρ).ge x.2⟩, ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range]
      refine ⟨z, Subtype.ext ?_⟩
      show ρ.norm z = x.1
      rw [Submodule.subtype_apply] at hz; exact hz
    · apply Subtype.ext; rfl

/-- `Ĥ⁰` of the three-term complex `auxS0` is the quotient of the invariants by the image
of the norm. -/
private noncomputable def aux_e4 (ρ : Representation ℤ G V) :
    letI : Module ℤ ↥(LinearMap.ker (auxS0 ρ).g.hom) := (LinearMap.ker (auxS0 ρ).g.hom).module
    letI : Module ℤ ↥(ρ.invariants) := (ρ.invariants).module
    ((LinearMap.ker (auxS0 ρ).g.hom) ⧸ LinearMap.range (auxS0 ρ).moduleCatToCycles) ≃ₗ[ℤ]
    (ρ.invariants ⧸ (LinearMap.range ρ.norm).comap ρ.invariants.subtype) := by
  letI : Module ℤ ↥(LinearMap.ker (auxS0 ρ).g.hom) := (LinearMap.ker (auxS0 ρ).g.hom).module
  letI : Module ℤ ↥(ρ.invariants) := (ρ.invariants).module
  let E : (LinearMap.ker (auxS0 ρ).g.hom ⧸
        (LinearMap.range (auxS0 ρ).moduleCatToCycles).toAddSubgroup) ≃+
      (ρ.invariants ⧸ ((LinearMap.range ρ.norm).comap ρ.invariants.subtype).toAddSubgroup) :=
    QuotientAddGroup.congr _ _ (aux_eKer ρ) (aux_map_P_eq_Q ρ)
  exact E.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance)

/-- The short complex `auxS0` is isomorphic, in degrees `-1, 0, 1`, to the Tate complex of
`Rep.of ρ`.  The isomorphisms in degree `-1, 0, 1` identify the inhomogeneous chains and
cochains with `V` and with `G → V`. -/
private noncomputable def aux_scIso (ρ : Representation ℤ G V) :
    (tateComplex (Rep.of ρ)).sc' (-1) 0 1 ≅ auxS0 ρ :=
  ShortComplex.isoMk (groupHomology.chainsIso₀ (Rep.of ρ)) (groupCohomology.cochainsIso₀ (Rep.of ρ))
    (groupCohomology.cochainsIso₁ (Rep.of ρ))
    (by
      show (groupHomology.chainsIso₀ (Rep.of ρ)).hom ≫ Rep.Hom.toModuleCatHom (Rep.of ρ).norm
        = Rep.tateNorm (Rep.of ρ) ≫ (groupCohomology.cochainsIso₀ (Rep.of ρ)).hom
      rw [Rep.tateNorm]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      show (groupCohomology.cochainsIso₀ (Rep.of ρ)).hom ≫ groupCohomology.d₀₁ (Rep.of ρ)
        = (groupCohomology.inhomogeneousCochains (Rep.of ρ)).d 0 1 ≫
            (groupCohomology.cochainsIso₁ (Rep.of ρ)).hom
      exact groupCohomology.comp_d₀₁_eq (Rep.of ρ))

theorem tateCohomology_zero_iso {G V : Type} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℤ V] (ρ : Representation ℤ G V) :
    Nonempty (letI : Module ℤ ↥(Representation.invariants ρ) := (Representation.invariants ρ).module
      tateCohomology (Rep.of ρ) 0 ≃ₗ[ℤ] (Representation.invariants ρ) ⧸
        (LinearMap.range (Representation.norm ρ)).comap (Representation.invariants ρ).subtype) := by
  classical
  letI : Module ℤ ↥(ρ.invariants) := (ρ.invariants).module
  haveI : Module ℤ ↥(LinearMap.ker (auxS0 ρ).g.hom) := (LinearMap.ker (auxS0 ρ).g.hom).module
  refine ⟨?_⟩
  let iso1 : (tateComplex (Rep.of ρ)).homology 0 ≅
      ((tateComplex (Rep.of ρ)).sc' (-1) 0 1).homology :=
    HomologicalComplex.homologyIsoSc' (tateComplex (Rep.of ρ)) (-1) 0 1
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel (-1) 0 from by
        simp [ComplexShape.up, ComplexShape.up']))
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel 0 1 from by
        simp [ComplexShape.up, ComplexShape.up']))
  let L1 : ((tateComplex (Rep.of ρ)).homology 0) ≃+
      (((tateComplex (Rep.of ρ)).sc' (-1) 0 1).homology) :=
    iso1.toLinearEquiv.toAddEquiv
  let L2 : (((tateComplex (Rep.of ρ)).sc' (-1) 0 1).homology) ≃+ (auxS0 ρ).homology :=
    (ShortComplex.homologyMapIso (aux_scIso ρ)).toLinearEquiv.toAddEquiv
  let L3 : (auxS0 ρ).homology ≃+ (auxS0 ρ).moduleCatLeftHomologyData.H :=
    (ShortComplex.moduleCatHomologyIso (auxS0 ρ)).toLinearEquiv.toAddEquiv
  let L4 : (auxS0 ρ).moduleCatLeftHomologyData.H ≃+
      (ρ.invariants ⧸ (LinearMap.range ρ.norm).comap ρ.invariants.subtype) :=
    (aux_e4 ρ).toAddEquiv
  exact (L1.trans (L2.trans (L3.trans L4))).toIntLinearEquiv
    (modM := inferInstance) (modM₂ := inferInstance)

end Commons.RepresentationTheory.TateCohomology