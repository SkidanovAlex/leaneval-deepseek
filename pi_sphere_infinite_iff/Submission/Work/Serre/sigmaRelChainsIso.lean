import Mathlib
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.cokernel_coproduct_iso
import Submission.Work.Serre.homology_coproduct_iso

/-!
# The singular chains of a disjoint union: naturality

The comparison isomorphism `chainSigmaIso` of `Work.Serre.sigmaChainsIso` is natural with respect to
inclusions of subspaces: it intertwines the inclusion of the relative chain complex of the pair
`(Σ i, X i, {x | x.2 ∈ A x.1})` with the coproduct of the inclusions of the pairs `(X i, A i)`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The naturality of the comparison map `sigmaToSSetHom` in its inverse form. -/
theorem sigmaToSSetHom_natural_inv (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫ Limits.Sigma.map (fun i =>
        TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i)))
      = TopCat.toSSet.map (sigmaSubtypeMap ι X A) ≫ (asIso (sigmaToSSetHom ι X)).inv := by
  rw [Iso.inv_comp_eq, asIso_hom, ← Category.assoc, sigmaToSSetHom_natural ι X A, Category.assoc]
  simp [asIso]

/-- The naturality of the comparison map `chainCoprodComp` in its inverse form. -/
theorem chainCoprodComp_natural_inv (R : Type) [CommRing R] (ι : Type) (Y Z : ι → SSet)
    (f : ∀ i, Y i ⟶ Z i) :
    (asIso (chainCoprodComp R ι Y)).inv ≫ Limits.Sigma.map (fun i =>
        ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map (f i))
      = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (Limits.Sigma.map f) ≫ (asIso (chainCoprodComp R ι Z)).inv := by
  rw [Iso.inv_comp_eq, asIso_hom, ← Category.assoc, chainCoprodComp_natural R ι Y Z f,
    Category.assoc]
  simp [asIso]

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **Naturality of `chainSigmaMap`** with respect to a family of subspaces: the comparison map
intertwines the inclusion `(Σ i, A i) ⊆ (Σ i, X i)` (transported along the canonical
homeomorphism `Σ i, A i ≅ {x | x.2 ∈ A x.1}`) with the coproduct of the inclusions
`A i ⊆ X i`. -/
theorem chainSigmaMap_natural_core (ι : Type) (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (A : ∀ i, Set (X i)) :
    (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i))))
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (sigmaSubtypeMap ι X A)) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) := by
  rw [Category.assoc, chainCoprodComp_natural_inv, ← Category.assoc, ← Functor.map_comp,
    sigmaToSSetHom_natural_inv, Functor.map_comp, Category.assoc]

/-- **Naturality of the comparison map `chainSigmaMap`** with respect to a family of subspaces. -/
theorem chainSigmaMap_natural (ι : Type) (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (A : ∀ i, Set (X i)) :
    (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (sigmaASHomeo ι X A).inv) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv)) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i))))
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (Σ i, X i))
          {x | x.2 ∈ A x.1})) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) := by
  rw [Category.assoc, chainSigmaMap_natural_core, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, sigmaASHomeo_inv_comp]

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **The relative singular chain complex of a disjoint union of pairs is the coproduct of the
relative singular chain complexes of the pieces.** -/
theorem relChains_coproduct_iso (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    Nonempty (Work.Cohomology.relChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} ≅
      ∐ fun i => Work.Cohomology.relChains (TopCat.of (X i)) (A i)) := by
  let F := ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  let m : ∀ i, F.obj (TopCat.toSSet.obj (TopCat.of (↥(A i)))) ⟶
      F.obj (TopCat.toSSet.obj (TopCat.of (X i))) :=
    fun i => F.map (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i)))
  have hsq : (F.map (TopCat.toSSet.map (sigmaASHomeo ι X A).inv) ≫
      (F.map (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv)) ≫
      Limits.Sigma.map m
      = F.map (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (Σ i, X i))
          {x | x.2 ∈ A x.1})) ≫
        (F.map (asIso (sigmaToSSetHom ι X)).inv ≫
          (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) :=
    chainSigmaMap_natural ι X A
  let e1 := cokernel.mapIso
    (f := F.map (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1})))
    (f' := Limits.Sigma.map m)
    (p := asIso (F.map (TopCat.toSSet.map (sigmaASHomeo ι X A).inv) ≫
      (F.map (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv)))
    (q := asIso (F.map (asIso (sigmaToSSetHom ι X)).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv))
    (w := by rw [asIso_hom, asIso_hom]; exact hsq.symm)
  obtain ⟨e2⟩ := cokernel_coproduct_iso (f := m)
  exact ⟨e1 ≪≫ e2 ≪≫ Limits.Sigma.mapIso (fun i => Iso.refl _)⟩

end

end Work.Serre
