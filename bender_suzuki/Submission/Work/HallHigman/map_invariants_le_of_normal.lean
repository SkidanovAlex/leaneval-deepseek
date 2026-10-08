import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- The fixed points of a normal subgroup form a `G`-invariant subspace. -/
lemma map_invariants_le_of_normal {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (P : Subgroup G) [P.Normal] (g : G) :
    (Representation.invariants (ρ.comp P.subtype)).map (ρ g) ≤
      Representation.invariants (ρ.comp P.subtype) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  rw [Representation.mem_invariants] at hv
  rw [Submodule.mem_comap, Representation.mem_invariants]
  intro p
  have hconj : g⁻¹ * (p : G) * g ∈ P := by
    simpa using (inferInstance : P.Normal).conj_mem (p : G) p.property g⁻¹
  have hp : ρ (g⁻¹ * (p : G) * g) v = v := hv ⟨g⁻¹ * (p : G) * g, hconj⟩
  calc ρ (p : G) (ρ g v)
      = ρ ((p : G) * g) v := by rw [← Module.End.mul_apply, ← map_mul]
    _ = ρ (g * (g⁻¹ * (p : G) * g)) v := by
          congr 1
          group
    _ = ρ g (ρ (g⁻¹ * (p : G) * g) v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g v := by rw [hp]

end Work.HallHigman
