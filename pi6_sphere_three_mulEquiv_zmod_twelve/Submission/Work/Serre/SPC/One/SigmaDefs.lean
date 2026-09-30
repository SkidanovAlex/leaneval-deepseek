import Mathlib
import Submission.Work.Cohomology.localHomology

set_option synthInstance.maxHeartbeats 400000


/-!
# The relative chain maps of a family of pairs, and of their disjoint union

`pairMap A B g hg` is the map of relative chain complexes `C_*(X,A) → C_*(Y,B)` induced by a
continuous map `g : X → Y` with `Set.MapsTo g A B`, and `sigmaPairMap` is the analogous map for the
disjoint union `Σ i, X i → Σ i, Y i` of a family.  These are the maps whose additivity (a coproduct
of isomorphisms on `H_m` is an isomorphism) is `Work.Serre.SPC.One.sigmaPairMap_isIso` and
`Work.Serre.SPC.One.sigmaPairMap_surjective`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

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

end Work.Serre.SPC.One
