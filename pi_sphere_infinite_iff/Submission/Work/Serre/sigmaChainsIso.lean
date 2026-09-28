import Mathlib
import Submission.Work.Serre.sigmaSSetDefs
import Submission.Work.Serre.sigmaToSSetHom_isIso
import Submission.Work.Serre.chainComplexFunctor_preserves_coproduct

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The singular chains of a disjoint union

The singular chain complex of a disjoint union `Σ i, X i` is the coproduct (direct sum) of the
singular chain complexes of the pieces, compatibly with the inclusions of subspaces.

The key inputs are

* `Work.Serre.sigmaToSSetHom_isIso` -- the singular simplicial set of a disjoint union is the
  coproduct of the singular simplicial sets of the pieces;
* `Work.Serre.chainComplexFunctor_preserves_coproduct` -- the simplicial chain functor preserves
  coproducts.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The canonical comparison map `∐_i F (Y_i) ⟶ F (∐_i Y_i)` of the simplicial chain functor `F`
is an isomorphism (here `F` is `SSet.chainComplexFunctor R` at the coefficient module `R`). -/
theorem chainCoprodComp_isIso (R : Type) [CommRing R] (ι : Type) (Y : ι → SSet) :
    IsIso (chainCoprodComp R ι Y) := by
  let F := ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  haveI := chainComplexFunctor_preserves_coproduct R ι
  let G : Discrete ι ⥤ SSet := Discrete.functor Y
  haveI : PreservesColimit G F := PreservesColimitsOfShape.preservesColimit
  let w : (G ⋙ F) ≅ Discrete.functor (fun i => F.obj (Y i)) := Discrete.compNatIsoDiscrete Y F
  haveI : HasColimit (G ⋙ F) := inferInstance
  have h : chainCoprodComp R ι Y =
      (preservesColimitIso F G ≪≫ HasColimit.isoOfNatIso w).inv := by
    apply Limits.Sigma.hom_ext
    intro j
    simp only [Sigma.ι_chainCoprodComp, Iso.trans_inv, ← Category.assoc,
      HasColimit.isoOfNatIso_ι_inv]
    rw [show w.inv.app ⟨j⟩ = 𝟙 _ from by simp [w, Discrete.compNatIsoDiscrete]]
    rw [Category.id_comp, ι_preservesColimitIso_inv]
  rw [h]
  infer_instance

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **Naturality of the comparison map** `sigmaToSSetHom` with respect to a family of subspaces. -/
theorem sigmaToSSetHom_natural (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    sigmaToSSetHom ι (fun i => ↥(A i)) ≫ TopCat.toSSet.map (sigmaSubtypeMap ι X A)
      = Limits.Sigma.map (fun i => TopCat.toSSet.map
          (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i))) ≫ sigmaToSSetHom ι X := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [← Category.assoc, sigmaToSSetHom, Limits.Sigma.ι_desc, ← Functor.map_comp]
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, sigmaToSSetHom, Limits.Sigma.ι_desc,
    ← Functor.map_comp]
  exact congrArg TopCat.toSSet.map (sigmaIota_subtype_comm ι X A j)

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- The comparison map `sigmaToSSetHom` is an isomorphism. -/
instance instIsIsoSigmaToSSetHom (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)] :
    IsIso (sigmaToSSetHom ι X) := sigmaToSSetHom_isIso ι X

/-- The comparison map `chainCoprodComp` is an isomorphism. -/
instance instIsIsoChainCoprodComp (R : Type) [CommRing R] (ι : Type) (Y : ι → SSet) :
    IsIso (chainCoprodComp R ι Y) := chainCoprodComp_isIso R ι Y

/-- The isomorphism `C_*(Σ i, Y i) ≅ ∐_i C_*(Y i)` expressing the singular chains of a disjoint
union as the direct sum of the singular chains of the pieces. -/
def chainSigmaIso (R : Type) [CommRing R] (ι : Type) (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)] :
    Work.Cohomology.singularChains R (TopCat.of (Σ i, Y i)) ≅
      ∐ fun i => Work.Cohomology.singularChains R (TopCat.of (Y i)) :=
  ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso
      (asIso (sigmaToSSetHom ι Y)).symm ≪≫
    (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).symm

/-- The canonical chain map underlying `chainSigmaIso`. -/
def chainSigmaMap (R : Type) [CommRing R] (ι : Type) (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)] :
    Work.Cohomology.singularChains R (TopCat.of (Σ i, Y i)) ⟶
      ∐ fun i => Work.Cohomology.singularChains R (TopCat.of (Y i)) :=
  (chainSigmaIso R ι Y).hom

theorem chainSigmaMap_isIso (R : Type) [CommRing R] (ι : Type) (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)] :
    IsIso (chainSigmaMap R ι Y) :=
  inferInstanceAs (IsIso (chainSigmaIso R ι Y).hom)

/-- The homeomorphism `Σ i, A i ≅ {x : Σ i, X i | x.2 ∈ A x.1}`. -/
def sigmaASHomeo (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)] (A : ∀ i, Set (X i)) :
    TopCat.of (Σ i, ↥(A i)) ≅ TopCat.of {x : Σ i, X i | x.2 ∈ A x.1} :=
  TopCat.isoOfHomeo
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      invFun := fun q => ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
      left_inv := fun p => by ext <;> rfl
      right_inv := fun q => by ext <;> rfl
      continuous_toFun := continuous_sigma_iff.2 (fun i => Continuous.subtype_mk
        ((continuous_sigmaMk (i := i)).comp continuous_subtype_val) _)
      continuous_invFun := by
        have hg : Topology.IsInducing (Sigma.map id (fun i => (Subtype.val : ↥(A i) → X i))) :=
          (Topology.isInducing_sigmaMap (f₁ := id) (f₂ := fun i => (Subtype.val : ↥(A i) → X i))
            Function.injective_id).2 (fun i => Topology.IsInducing.subtypeVal)
        refine (hg.continuous_iff).mpr ?_
        have h : (Sigma.map id (fun i => (Subtype.val : ↥(A i) → X i))) ∘
              (fun q : ↥{x : Σ i, X i | x.2 ∈ A x.1} =>
                (⟨q.1.1, ⟨q.1.2, q.2⟩⟩ : Σ i, ↥(A i))) = Subtype.val := by
          funext q
          rfl
        rw [h]
        exact continuous_subtype_val }

theorem sigmaASHomeo_inv_comp (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    (sigmaASHomeo ι X A).inv ≫ sigmaSubtypeMap ι X A
      = Work.Cohomology.subtypeIncl (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} := by
  ext x
  · rfl
  · exact HEq.rfl

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- Naturality of the comparison map `chainCoprodComp` with respect to a family of morphisms of
simplicial sets. -/
theorem chainCoprodComp_natural (R : Type) [CommRing R] (ι : Type) (Y Z : ι → SSet)
    (f : ∀ i, Y i ⟶ Z i) :
    chainCoprodComp R ι Y ≫ ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (Limits.Sigma.map f)
      = Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj
          (ModuleCat.of R R)).map (f i)) ≫ chainCoprodComp R ι Z := by
  apply Limits.Sigma.hom_ext
  intro j
  calc Sigma.ι _ j ≫ (chainCoprodComp R ι Y ≫ ((SSet.chainComplexFunctor (ModuleCat R)).obj
          (ModuleCat.of R R)).map (Limits.Sigma.map f))
      = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map (Sigma.ι Y j) ≫
          ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
            (Limits.Sigma.map f) := by
        rw [← Category.assoc, Sigma.ι_chainCoprodComp]
    _ = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (Sigma.ι Y j ≫ Limits.Sigma.map f) := by rw [← Functor.map_comp]
    _ = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (f j ≫ Sigma.ι Z j) := by rw [Limits.Sigma.ι_map]
    _ = Sigma.ι _ j ≫ (Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj
            (ModuleCat.of R R)).map (f i)) ≫ chainCoprodComp R ι Z) := by
        rw [Functor.map_comp, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
          Sigma.ι_chainCoprodComp, ← Functor.map_comp]

/-- The characterisation of `chainSigmaMap` on the defining maps. -/
theorem chainSigmaMap_eq (R : Type) [CommRing R] (ι : Type) (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)] :
    chainSigmaMap R ι Y =
      ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (asIso (sigmaToSSetHom ι Y)).inv ≫
        (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).inv := rfl

end

end Work.Serre
