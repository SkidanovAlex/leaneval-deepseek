import Mathlib
import Submission.Work.Serre.SPC.One.Defs
import Submission.Work.Serre.cubePairDefs

set_option synthInstance.maxHeartbeats 400000


/-!
# The disc model pair map (the `1`-cell local model)

For a continuous map `p : E → B` and a map `χ : D¹ → B`, this file defines the **map of pairs**

  `(χ^*E, χ^*E|_{S⁰}) ⟶ (D¹, S⁰)`

induced by the fibration `p` (i.e. by the projection `χ^*E → D¹`) on relative singular chains.

This is the `D = 1` analogue of `Work.Serre.cubePairMap 1`, and the statement that it is an
isomorphism on homology in degrees `< 1 + φ` (and surjective in degree `1 + φ`) when the fibres are
homologically `φ`-connected is the local input of the `1`-cell step; it is proved in
`Submission/Work/Serre/SPC/One/DiscModel.lean` by transporting `Work.Serre.SPC.cubePairStrong 1`
along a homeomorphism `I¹ ≅ D¹`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

/-- The boundary `S⁰ = {±1}` of the model interval, as a subset of `D¹`. -/
def cellS0Set : Set cellD1 := Set.range cellS0ToD1

@[simp] theorem mem_cellS0Set {x : cellD1} : x ∈ cellS0Set ↔ ∃ z : cellS0, cellS0ToD1 z = x :=
  Iff.rfl

/-- The preimage of the boundary of the interval in the pullback of `p` along `χ`. -/
def pbPreOne {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (χ : C(cellD1, B)) : Set (Work.StemsB.Pullback p χ) :=
  {x | Work.StemsB.pullbackSnd p χ x ∈ cellS0Set}

/-- The restriction of the projection `χ^*E → D¹` to the preimage of the boundary. -/
def discPairMapRel {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (χ : C(cellD1, B)) :
    C(↥(pbPreOne p χ), ↥cellS0Set) :=
  ⟨fun x => ⟨(Work.StemsB.pullbackSnd p χ) x.1, x.2⟩, by
    exact Continuous.subtype_mk
      ((Work.StemsB.pullbackSnd p χ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩

/-- **The map of pairs `(χ^*E, χ^*E|_{S⁰}) → (D¹, S⁰)`** induced by a continuous map `p : E → B`
along a map `χ : D¹ → B`. -/
noncomputable def discPairMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (χ : C(cellD1, B)) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p χ)) (pbPreOne p χ) ⟶
      Work.Cohomology.relChains (TopCat.of cellD1) cellS0Set :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback p χ)) (TopCat.of cellD1)
    (pbPreOne p χ) cellS0Set
    (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
    (TopCat.ofHom (discPairMapRel p χ))
    (by ext x; rfl)

end

end Work.Serre.SPC.One
