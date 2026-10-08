import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PGroup.Symplectic

/-- If `C` is a characteristic subgroup of `X`, then any characteristic subgroup of `↥C`
is characteristic in `X` (as the image along `C.subtype`). -/
theorem map_subtype_characteristic {X : Type*} [Group X] {C : Subgroup X} (hC : C.Characteristic)
    {A : Subgroup ↥C} (hA : A.Characteristic) : (A.map C.subtype).Characteristic := by
  haveI : C.Characteristic := hC
  haveI : A.Characteristic := hA
  infer_instance

theorem of_characteristic {X : Type*} [Group X] {C : Subgroup X} (hC : C.Characteristic)
    (h : ∀ A : Subgroup X, A.Characteristic → IsMulCommutative A → ∃ a : X, A = Subgroup.zpowers a) :
    ∀ A : Subgroup ↥C, A.Characteristic → IsMulCommutative A → ∃ a : ↥C, A = Subgroup.zpowers a := by
  intro A hAchar hAcomm
  have hBchar : (A.map C.subtype).Characteristic := map_subtype_characteristic hC hAchar
  have hBcomm : IsMulCommutative (A.map C.subtype) := by
    rw [isMulCommutative_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    show (a : X) * (b : X) = (b : X) * (a : X)
    exact congrArg (fun z : A => (z : X)) (isMulCommutative_iff.mp hAcomm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨a, ha⟩ := h (A.map C.subtype) hBchar hBcomm
  have haC : a ∈ C := Subgroup.map_subtype_le A (ha ▸ Subgroup.mem_zpowers a)
  refine ⟨⟨a, haC⟩, ?_⟩
  apply Subgroup.map_injective (f := C.subtype) (Subgroup.subtype_injective C)
  rw [MonoidHom.map_zpowers, ha]
  rfl

end Work.PGroup.Symplectic
