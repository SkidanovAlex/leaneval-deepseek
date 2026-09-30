import Mathlib
import Submission.Work.Serre.sigmaSSetDefs

/-!
# Naturality of the coproduct comparison `sigmaToSSetHom` for a *general* family of maps

`Work.Serre.sigmaToSSetHom ι X : ∐_i S(X_i) ⟶ S(Σ_i X_i)` is the comparison map whose
isomorphism is `Work.Serre.sigmaToSSetHom_isIso`.  `Work.Serre.sigmaToSSetHom_natural` records its
naturality for a family of *subspaces* (`A i ⊆ X i`), which is what the relative-chain decomposition
`Work.Serre.relChains_coproduct_iso` needs.

The additivity over a disjoint union for a *general* family of maps of pairs
(`Work.Serre.CellStep.sigmaAdditivity`, the step of the rational cell step which splits the relative
chain complex of a cell attachment as the direct sum of the per-cell complexes) needs the same
naturality for a general family `f : ∀ i, C(X i, Y i)`.  This module provides it, together with the
point-set identity behind it (the analogue of `Work.Serre.sigmaIota_subtype_comm`).

Both statements are generic (they mention only `Work.Serre.sigmaToSSetHom`/`sigmaMapTop`), so they
are stable under any further change to the cell-step files.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB.CellStep

noncomputable section

/-- The point-set identity behind the naturality of `sigmaToSSetHom`: the inclusion of the `j`-th
summand followed by `sigmaMapTop` is the map `f j` followed by the inclusion of the `j`-th
summand. -/
theorem sigmaIota_mapTop_comm (ι : Type) (X Y : ι → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) (j : ι) :
    (TopCat.sigmaι (fun i => TopCat.of (X i)) j : TopCat.of (X j) ⟶ TopCat.of (Σ i, X i))
        ≫ Work.Serre.sigmaMapTop ι X Y f
      = (TopCat.ofHom (f j)) ≫ (TopCat.sigmaι (fun i => TopCat.of (Y i)) j :
          TopCat.of (Y j) ⟶ TopCat.of (Σ i, Y i)) := by
  ext x
  · rfl
  · exact HEq.rfl

/-- **Naturality of the comparison map `sigmaToSSetHom` with respect to a general family of
continuous maps.** -/
theorem sigmaToSSetHom_natural_gen (ι : Type) (X Y : ι → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) :
    Work.Serre.sigmaToSSetHom ι X ≫ TopCat.toSSet.map (Work.Serre.sigmaMapTop ι X Y f)
      = Limits.Sigma.map (fun i => TopCat.toSSet.map (TopCat.ofHom (f i)))
          ≫ Work.Serre.sigmaToSSetHom ι Y := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [← Category.assoc, Work.Serre.sigmaToSSetHom, Limits.Sigma.ι_desc, ← Functor.map_comp]
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Work.Serre.sigmaToSSetHom,
    Limits.Sigma.ι_desc, ← Functor.map_comp]
  exact congrArg TopCat.toSSet.map (sigmaIota_mapTop_comm ι X Y f j)

end

end Work.StemsB.CellStep
