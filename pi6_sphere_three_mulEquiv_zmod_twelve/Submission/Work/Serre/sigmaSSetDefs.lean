import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The singular chains of a disjoint union: vocabulary

This file sets up the vocabulary for the lemma `Work.Serre.sigmaRelHomologyIso`, namely that the
relative singular chain complex of a disjoint union of pairs is the direct sum of the relative
singular chain complexes of the pieces.

The main definition here is `Work.Serre.sigmaToSSetHom`, the canonical comparison map

  `∐_i S(X_i)  ⟶  S(Σ_i X_i)`

from the coproduct of the singular simplicial sets of the pieces to the singular simplicial set of
the disjoint union.  It is defined by the universal property of the coproduct; the mathematical
content (that it is an isomorphism, because the standard simplices are connected) is
`Work.Serre.sigmaToSSetHom_isIso`.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The canonical comparison map `∐_i S(X i) ⟶ S(Σ i, X i)` from the coproduct of the singular
simplicial sets of the pieces to the singular simplicial set of the disjoint union. -/
def sigmaToSSetHom (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)] :
    (∐ fun i => TopCat.toSSet.obj (TopCat.of (X i))) ⟶ TopCat.toSSet.obj (TopCat.of (Σ i, X i)) :=
  Limits.Sigma.desc (fun i => TopCat.toSSet.map (TopCat.sigmaι (fun i => TopCat.of (X i)) i))

/-- The canonical continuous map `Σ_i A_i ⟶ Σ_i X_i` for a family of subsets. -/
def sigmaSubtypeMap (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)] (A : ∀ i, Set (X i)) :
    TopCat.of (Σ i, A i) ⟶ TopCat.of (Σ i, X i) :=
  TopCat.ofHom ⟨Sigma.map id (fun i => Subtype.val), continuous_sigma_map.2 fun _ => continuous_subtype_val⟩

/-- The canonical continuous map `Σ_i X_i ⟶ Σ_i Y_i` for a family of continuous maps. -/
def sigmaMapTop (ι : Type) (X Y : ι → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) :
    TopCat.of (Σ i, X i) ⟶ TopCat.of (Σ i, Y i) :=
  TopCat.ofHom ⟨Sigma.map id (fun i => f i), continuous_sigma_map.2 fun i => (f i).continuous⟩

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- The canonical comparison map `∐_i F (Y_i) ⟶ F (∐_i Y_i)` for the simplicial chain functor
`F` with coefficients in `R`. -/
def chainCoprodComp (R : Type) [CommRing R] (ι : Type) (Y : ι → SSet) :
    (∐ fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj (Y i)) ⟶
      ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj (∐ Y) :=
  Limits.Sigma.desc (fun i =>
    ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
      (CategoryTheory.Limits.Sigma.ι Y i))

@[reassoc (attr := simp)]
theorem Sigma.ι_chainCoprodComp (R : Type) [CommRing R] (ι : Type) (Y : ι → SSet) (i : ι) :
    Limits.Sigma.ι (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj
        (ModuleCat.of R R)).obj (Y i)) i ≫ chainCoprodComp R ι Y =
      ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (CategoryTheory.Limits.Sigma.ι Y i) :=
  Limits.Sigma.ι_desc _ _

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- The summand inclusions of `Σ i, A i` and of `Σ i, X i` are compatible with the canonical map
`Σ i, A i ⟶ Σ i, X i`. -/
theorem sigmaIota_subtype_comm (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) (j : ι) :
    (TopCat.sigmaι (fun i => TopCat.of (A i)) j : TopCat.of (A j) ⟶ TopCat.of (Σ i, A i))
        ≫ sigmaSubtypeMap ι X A
      = (Work.Cohomology.subtypeIncl (TopCat.of (X j)) (A j)) ≫
          (TopCat.sigmaι (fun i => TopCat.of (X i)) j : TopCat.of (X j) ⟶ TopCat.of (Σ i, X i)) := by
  ext x
  · rfl
  · exact HEq.rfl

end

end Work.Serre
