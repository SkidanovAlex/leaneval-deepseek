import Mathlib
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.sigmaToSSetHom_isIso
import Submission.Work.Serre.chainComplexFunctor_preserves_coproduct
import Submission.Work.Serre.cokernel_coproduct_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of relative homology over a disjoint union

The relative singular chain complex of a disjoint union of pairs `(Σ i, X i, Σ i, A i)` is the
direct sum of the relative chain complexes of the pieces, and the map induced by a *family* of maps
of pairs is the coproduct of the individual maps (`Work.Serre.sigmaPairMap`).  Consequently the
union map is an isomorphism on homology in degree `m` as soon as every piece map is
(`Work.Serre.sigmaAdditivity`, the statement delegated in this file).

`Work.Serre.pairMap` is the relative chain map of a single continuous map of pairs, in the
"`Set.MapsTo`" form used throughout the cell-step argument.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The relative chain map of a continuous map of pairs `g : (X,A) → (Y,B)`, in the
"`Set.MapsTo`" form. -/
noncomputable def pairMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    Work.Cohomology.relChains (TopCat.of X) A ⟶ Work.Cohomology.relChains (TopCat.of Y) B :=
  Work.Cohomology.relChainsMapOf (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)

/-- The map of pairs of a family of continuous maps of pairs, on the disjoint unions. -/
noncomputable def sigmaPairMap {ι : Type} (X Y : ι → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) :
    Work.Cohomology.relChains (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} ⟶
      Work.Cohomology.relChains (TopCat.of (Σ i, Y i)) {x : Σ i, Y i | x.2 ∈ B x.1} :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
    {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, Y i | x.2 ∈ B x.1}
    (TopCat.ofHom ⟨Sigma.map id (fun i => g i), continuous_sigma_map.2 fun i => (g i).continuous⟩)
    (TopCat.ofHom ⟨fun x => ⟨Sigma.map id (fun i => g i) x.1, (hg x.1.1) x.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_sigma_map.2 fun i => (g i).continuous).comp continuous_subtype_val⟩)
    (by ext x <;> rfl)

end

end Work.Serre
