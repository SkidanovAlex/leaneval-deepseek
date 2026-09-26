import Mathlib.Topology.Constructions

namespace Commons.Topology.Homeomorph

/-- A homeomorphism `e : X ≃ₜ Y` restricts to a homeomorphism between the subtype of
`X` lying over `P ⊆ Y` and the subtype `P` itself. -/
theorem subtype_preimage_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (P : Set Y) :
    Nonempty ({x : X // e x ∈ P} ≃ₜ {y : Y // y ∈ P}) := by
  let F : {x : X // e x ∈ P} ≃ {y : Y // y ∈ P} :=
    { toFun := Subtype.map e (fun _ hx => hx)
      invFun := Subtype.map e.symm (fun y hy => by simpa using hy)
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y.1 }
  refine ⟨Homeomorph.mk F ?_ ?_⟩
  · exact Continuous.subtype_map e.continuous (fun _ hx => hx)
  · exact Continuous.subtype_map e.symm.continuous (fun y hy => by simpa using hy)

end Commons.Topology.Homeomorph