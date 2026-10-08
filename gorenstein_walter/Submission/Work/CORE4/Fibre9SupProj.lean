import Mathlib

namespace Work.CORE4

/-- If `π : ↥(P ⊔ E) →* ↥E` is a projection of `P ⊔ E` onto `E` whose "kernel"
lies in `P` (in the sense that `x * (π x)⁻¹ ∈ P` for every `x`), and `Y ≤ P ⊔ E`,
then `Y` and its image `π Y` generate the same group together with `P`.

This is a general group-theoretic fact: every element of `P ⊔ E` differs from its
image under `π` by an element of `P`, so `Y` and `π(Y)` coincide modulo `P`. -/
theorem Fibre9SupProj {G : Type} [Group G] {P E Y : Subgroup G}
    (π : ↥(P ⊔ E) →* ↥E)
    (hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P)
    (hY : Y ≤ P ⊔ E) :
    P ⊔ Y = P ⊔ Subgroup.map E.subtype ((Y.subgroupOf (P ⊔ E)).map π) := by
  apply le_antisymm
  · -- `Y ≤ P ⊔ π(Y)`: each `y ∈ Y` equals `(y * (π y)⁻¹) * π y`.
    apply sup_le le_sup_left
    intro y hy
    have hyQ : y ∈ P ⊔ E := hY hy
    set x : ↥(P ⊔ E) := ⟨y, hyQ⟩
    have hP : y * (((π x : ↥E) : G))⁻¹ ∈ P := hproj x
    have hmem : (((π x : ↥E) : G)) ∈
        Subgroup.map E.subtype ((Y.subgroupOf (P ⊔ E)).map π) := by
      rw [Subgroup.mem_map]
      refine ⟨π x, ?_, rfl⟩
      rw [Subgroup.mem_map]
      exact ⟨x, by rw [Subgroup.mem_subgroupOf]; exact hy, rfl⟩
    have heq : y = (y * (((π x : ↥E) : G))⁻¹) * (((π x : ↥E) : G)) := by group
    rw [heq]
    exact Subgroup.mul_mem_sup hP hmem
  · -- `π(Y) ≤ P ⊔ Y`: each `π y` equals `(π y * y⁻¹) * y`.
    apply sup_le le_sup_left
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [Subgroup.mem_subgroupOf] at hx
    have hP : (((π x : ↥E) : G)) * (x : G)⁻¹ ∈ P := by
      have h := inv_mem (hproj x)
      simpa [mul_inv_rev] using h
    have heq : E.subtype (π x) = (((π x : ↥E) : G) * (x : G)⁻¹) * (x : G) := by
      rw [Subgroup.subtype_apply]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hP hx

end Work.CORE4
