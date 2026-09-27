import Mathlib

namespace Work.Drive

open Set in
/-- **An open quotient map restricts to an open quotient map on a saturated open set.**  If `q : X → Y` is an
open quotient map, `A ⊆ X` is open and saturated for `q` (i.e. `q ⁻¹' (q '' A) = A`), then the restriction
`A → q '' A`, `v ↦ q v`, of `q` is again an open quotient map. -/
theorem isOpenQuotientMap_subtype_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsOpenQuotientMap q) {A : Set X} (hA : IsOpen A)
    (hsat : q ⁻¹' (q '' A) = A) :
    IsOpenQuotientMap (fun v : A => (⟨q v.1, v.1, v.2, rfl⟩ : q '' A)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · show Continuous (Subtype.map q (fun x hx => (⟨x, hx, rfl⟩ : q x ∈ q '' A)))
    exact hq.continuous.subtype_map fun x hx => ⟨x, hx, rfl⟩
  · exact hq.isOpenMap.subtype_map (s := A) (t := q '' A) hA fun x hx => ⟨x, hx, rfl⟩

end Work.Drive
