import Mathlib
import Submission.Work.Serre.DiscPair.thomRVDefs
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.DiscPair

set_option maxHeartbeats 800000

/-- **The mapping cylinder of `q|_V` is the part of the mapping cylinder of `q` over an open `V`**:
the open companion of `Work.Serre.DiscPair.cylPreimageHomeo` (which is stated for *closed* `S`).
It is the map `cylPreimageLift q V`, which is a bijective quotient map because the restriction of
the quotient map `cylMk q` to the *saturated open* set
`cylPreSet q V = cylMk q ⁻¹' ((cylRetract q) ⁻¹' V)` is a quotient map
(`Topology.IsQuotientMap.restrictPreimage_isOpen`, since `(cylRetract q) ⁻¹' V` is open), so
`isQuotientMap_cylPreimageLift` applies.  The two compatibility statements are the open analogues
of `cylPreimageHomeo_range` and `cylRetract_cylPreimageLift_qS`. -/
theorem cylPreimageHomeoOpen {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ]
    (q : C(X, Γ)) (V : Set Γ) (hV : IsOpen V) :
    ∃ e : Work.Serre.cyl (Work.Serre.restrictFibre q V) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' V),
      (∀ y, y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)) ↔
        e y ∈ Work.Serre.DiscPair.cylPreBot q V) ∧
      (∀ y, Work.Serre.DiscPair.cylPreRetract q V (e y) =
        Work.Serre.cylRetract (Work.Serre.restrictFibre q V) y) := by
  -- the restriction of the quotient map `cylMk q` to the preimage of the *open* set
  -- `(cylRetract q) ⁻¹' V` is a quotient map
  have hquot : Topology.IsQuotientMap (Work.Serre.DiscPair.cylPreSetRestrict q V) :=
    Topology.IsQuotientMap.restrictPreimage_isOpen (f := Work.Serre.cylMk q)
      isQuotientMap_quotient_mk' (hV.preimage (Work.Serre.cylRetract q).continuous)
  have hq : Topology.IsQuotientMap (Work.Serre.DiscPair.cylPreimageLift q V) :=
    Work.Serre.DiscPair.isQuotientMap_cylPreimageLift q V hquot
  have hinj : Function.Injective (Work.Serre.DiscPair.cylPreimageLift q V) :=
    Work.Serre.DiscPair.cylPreimageLift_injective q V
  -- `cylPreimageLift q V` is a bijective quotient map, hence a homeomorphism
  let e : Work.Serre.cyl (Work.Serre.restrictFibre q V) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' V) :=
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hinj⟩).homeomorph
      (Work.Serre.DiscPair.cylPreimageLift q V)
  refine ⟨e, ?_, ?_⟩
  · -- the bottom copy is matched
    intro y
    have hy : (e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) =
        Work.Serre.DiscPair.cylPreimageLift q V y := rfl
    show y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.DiscPair.qS q V)) ↔
      ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q) ∈
        Set.range (Work.Serre.cylIncl q)
    rw [hy]
    exact (Work.Serre.DiscPair.cylPreimageLift_range q V y).symm
  · -- the retractions agree
    intro y
    refine Subtype.ext ?_
    show Work.Serre.cylRetract q ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
      = ((Work.Serre.cylRetract (Work.Serre.DiscPair.qS q V) y : ↥V) : Γ)
    rw [show ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
        = (Work.Serre.DiscPair.cylPreimageLift q V y : Work.Serre.cyl q) from rfl]
    exact Work.Serre.DiscPair.cylRetract_cylPreimageLift_qS q V y

end Work.Serre.DiscPair
