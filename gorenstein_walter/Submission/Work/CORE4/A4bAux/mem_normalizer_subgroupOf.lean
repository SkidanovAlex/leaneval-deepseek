import Mathlib

namespace Work.CORE4.A4bAux

theorem mem_normalizer_subgroupOf {G : Type*} [Group G] {E V : Subgroup G} (hVE : V ≤ E)
    (x : ↥E) : x ∈ Subgroup.normalizer ((V.subgroupOf E : Subgroup ↥E) : Set ↥E) ↔
      (x : G) ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx h
    constructor
    · intro hhV
      have hE : h ∈ E := hVE hhV
      have h1 := (hx ⟨h, hE⟩).mp hhV
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · intro hh
      have hxE : (x : G) ∈ E := x.2
      have hmem : (x : G)⁻¹ * (↑x * h * ↑x⁻¹) * (x : G) ∈ E :=
        E.mul_mem (E.mul_mem (E.inv_mem hxE) (hVE hh)) hxE
      have hE : h ∈ E := by simpa [mul_assoc] using hmem
      have h2 := (hx ⟨h, hE⟩).mpr ?_
      · exact h2
      · rw [Subgroup.mem_subgroupOf]; simpa using hh
  · intro hx h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hx h

end Work.CORE4.A4bAux
