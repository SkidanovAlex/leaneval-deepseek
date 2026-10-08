import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step5

theorem noncomm_of_map_eq {M A : Type*} [Group M] [Group A] {K : Subgroup M} (f : M →* A)
    (Λ : Subgroup A) (hmap : Subgroup.map f K = Λ)
    (hnab : ∃ a b : ↥Λ, a * b ≠ b * a) : ∃ a b : ↥K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨a, b, hab⟩ := hnab
  have ha : (a : A) ∈ Subgroup.map f K := by rw [hmap]; exact a.2
  have hb : (b : A) ∈ Subgroup.map f K := by rw [hmap]; exact b.2
  rw [Subgroup.mem_map] at ha hb
  obtain ⟨x, hx, hfx⟩ := ha
  obtain ⟨y, hy, hfy⟩ := hb
  have hxy : (⟨x, hx⟩ : ↥K) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := h _ _
  have hkey : f (x * y) = f (y * x) := by
    have := congrArg (fun t : ↥K => f (t : M)) hxy
    simpa using this
  exact hab (Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hfx, ← hfy, ← map_mul, ← map_mul]
    exact hkey))

end Work.Hering.Step5
