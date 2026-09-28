import Mathlib
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreE2b

/-!
# The pair map of the cube pair, relative to the base

For a continuous map `p : E → B` and a map `τ : I^D → B`, this file defines the **map of pairs**

  `(τ^*E, τ^*E|_{∂I^D}) ⟶ (I^D, ∂I^D)`

induced by the fibration `p` (i.e. by the projection `τ^*E → I^D`), on relative singular chains.

This is the map whose being a quasi-isomorphism in the range `< D + f` (for a fibre of `p` over
the image of `τ` which is homologically `f`-connected) is statement `(P_D)` of the cell-attachment
argument of the Serre exact sequence in the stable range: see
`Submission/Work/Serre/StableExact.lean` and the delegated lemma
`Work.Serre.cubeRelIso` (`Submission/Work/Serre/cubeRelIso.lean`).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The restriction of the projection `τ^*E → I^D` to the preimage of the boundary, as a map of
the relative parts. -/
def cubePairMapRel {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (D : ℕ)
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B)) :
    C(↥(pbPre p τ (cubeBdryS D)), ↥(cubeBdryS D)) :=
  ⟨fun x => ⟨Work.StemsB.pullbackSnd p τ x.1, x.2⟩, by
    exact Continuous.subtype_mk
      ((Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩

/-- **The map of pairs `(τ^*E, τ^*E|_{∂I^D}) → (I^D, ∂I^D)`** induced by a continuous map
`p : E → B` along a map `τ : I^D → B`. -/
noncomputable def cubePairMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (D : ℕ)
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B)) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ)) (pbPre p τ (cubeBdryS D)) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D)) (cubeBdryS D) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback p τ))
    (TopCat.of (Work.Stems.Cubical.IC D)) (pbPre p τ (cubeBdryS D)) (cubeBdryS D)
    (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (TopCat.ofHom (cubePairMapRel D p τ))
    (by ext x; rfl)

end

end Work.Serre
