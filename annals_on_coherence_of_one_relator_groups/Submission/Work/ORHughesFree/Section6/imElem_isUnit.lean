import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- The image of a product of group-like units: `imElem φ (u * v) = imElem φ u * imElem φ v`.
This is a local restatement of `Work.ORHughesFree.Section6.imElem_mul`; it is proved here so
that `imElem_isUnit` is self-contained. -/
theorem imElem_mul_of_unitOf (φ : MonoidAlgebra K G →+* U) (u v : Kˣ × G) :
    Work.ORHughesFree.imElem φ (u * v) =
      Work.ORHughesFree.imElem φ u * Work.ORHughesFree.imElem φ v := by
  apply Subtype.ext
  show φ (Work.ORHughesFree.unitOf (u * v)) =
    φ (Work.ORHughesFree.unitOf u) * φ (Work.ORHughesFree.unitOf v)
  rw [Work.ORHughesFree.unitOf_mul, map_mul]

/-- The image of the identity group-like unit is `1`. -/
theorem imElem_one_of_unitOf (φ : MonoidAlgebra K G →+* U) :
    Work.ORHughesFree.imElem φ 1 = 1 := by
  apply Subtype.ext
  show φ (Work.ORHughesFree.unitOf (1 : Kˣ × G)) = (1 : U)
  rw [Work.ORHughesFree.unitOf_one, map_one]

theorem imElem_isUnit {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G) :
    IsUnit (Work.ORHughesFree.imElem φ u) ∧
      ∀ h : IsUnit (Work.ORHughesFree.imElem φ u),
        ↑h.unit⁻¹ = Work.ORHughesFree.imElem φ u⁻¹ := by
  have hright : Work.ORHughesFree.imElem φ u * Work.ORHughesFree.imElem φ u⁻¹ = 1 := by
    rw [← imElem_mul_of_unitOf, mul_inv_cancel, imElem_one_of_unitOf]
  have hleft : Work.ORHughesFree.imElem φ u⁻¹ * Work.ORHughesFree.imElem φ u = 1 := by
    rw [← imElem_mul_of_unitOf, inv_mul_cancel, imElem_one_of_unitOf]
  refine ⟨⟨⟨Work.ORHughesFree.imElem φ u, Work.ORHughesFree.imElem φ u⁻¹, hright, hleft⟩,
    rfl⟩, ?_⟩
  intro h
  have hw : h.unit =
      ⟨Work.ORHughesFree.imElem φ u, Work.ORHughesFree.imElem φ u⁻¹, hright, hleft⟩ :=
    Units.ext (IsUnit.unit_spec h)
  exact (congrArg (fun x : (↥(Work.ORHughesFree.divisionClosure (Set.range φ)))ˣ =>
    (↑x⁻¹ : ↥(Work.ORHughesFree.divisionClosure (Set.range φ)))) hw).trans rfl

end Work.ORHughesFree.Section6
