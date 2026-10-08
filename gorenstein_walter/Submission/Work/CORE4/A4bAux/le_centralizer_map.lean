import Mathlib

namespace Work.CORE4.A4bAux

theorem le_centralizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    A.map f ≤ Subgroup.centralizer ((B.map f : Subgroup H) : Set H) := by
  intro a ha
  rw [Subgroup.mem_map] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [SetLike.mem_coe] at hy ⊢
  rw [Subgroup.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hh : z * x = x * z := (Subgroup.mem_centralizer_iff.mp (h hx)) z hz
  rw [← map_mul, ← map_mul, hh]

end Work.CORE4.A4bAux
