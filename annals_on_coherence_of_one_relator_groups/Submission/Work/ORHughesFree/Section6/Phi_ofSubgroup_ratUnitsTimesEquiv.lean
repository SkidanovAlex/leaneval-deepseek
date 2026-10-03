import Mathlib
import Submission.Work.ORHughesFree.Section6.UnitsTimesEquiv
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Reduce
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Section6.Phi_subgroup_mem
import Submission.Work.ORHughesFree.Section6.treeG_le_treeG_of_subgroup

namespace Work.ORHughesFree.Section6

/-- **The `H`-structure maps of `D_{K[G],U}` agree.**  The two ways of evaluating `Rat(E^× H)` in
`D_{K[G],U}` — through the subgroup `↥(E^× H) ≤ E^× G` of the units of the crossed product
(`Phi φ ∘ ofSubgroup ∘ ratUnitsTimesEquiv`) and through the group algebra of `H` inside that of `G`
(`Phi (φ ∘ inducedMapRing H)`, composed with the inclusion `D_{K[H],U} ⊆ D_{K[G],U}`) —
coincide.  Both are morphisms of rational `Kˣ × H`-semirings into `D_{K[G],U}` (for the
restriction of `Section6.ratStruct φ` to `↥(unitsTimesSubgroup H)`, transported along
`ratUnitsTimesEquiv`), and they agree on the images of the group elements: `ofGroup u` maps to
`φ (unitOf (unitsTimesMulEquiv u))` on the one hand and to `φ (inducedMapRing H (unitOf u)) =
φ (unitOf (unitsTimesMulEquiv u))` on the other (using `ratUnitsTimesEquiv_ofGroup` and that
`inducedMapRing H` sends `single h λ` to `single ↑h λ`); uniqueness of the universal morphism
(`RatU.lift_existsUnique`) then gives the equality.  The file `Section6/Phi_subgroup_mem.lean`
contains the surrounding machinery (`heq`, `toDG_ratOpClosure`, `ratStructSubgroup`). -/
theorem Phi_ofSubgroup_ratUnitsTimesEquiv {K : Type} [Field K] {G : Type} [Group G] {U : Type}
    [Ring U] (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (β : RatU (Kˣ × H)) :
    ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H β)) : U)
      = ((Phi (φ.comp (inducedMapRing H))) β : U) := by
  -- The two halves of the compatibility square (proved for `Section6.treeG_le_treeG_of_subgroup`):
  -- `toDG φ H` intertwines `RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)` with `Phi φ` composed
  -- with `ofSubgroup`, and that same lift computes `Phi (φ ∘ K[↥H] ↪ K[G])` after transporting
  -- along `ratUnitsTimesEquiv`.
  have hlift : RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
        (ratUnitsTimesEquiv (K := K) H β)
      = Phi (φ.comp (inducedMapRing (K := K) H)) β :=
    lift_ratStructSubgroup_ratUnitsTimesEquiv φ H β
  have htoDG : toDG φ H (Phi (φ.comp (inducedMapRing (K := K) H)) β)
      = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H β)) := by
    rw [← hlift]
    exact toDG_lift_ratStructSubgroup φ H (ratUnitsTimesEquiv (K := K) H β)
  calc ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H β)) : U)
      = ((toDG φ H (Phi (φ.comp (inducedMapRing (K := K) H)) β) : ↥(DGU φ)) : U) :=
        congrArg (fun z : ↥(DGU φ) => (z : U)) htoDG.symm
    _ = ((Phi (φ.comp (inducedMapRing (K := K) H)) β : ↥(DHU φ H)) : U) :=
        toDG_coe φ H _

end Work.ORHughesFree.Section6
