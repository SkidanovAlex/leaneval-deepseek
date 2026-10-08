import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2.MyAux

theorem mulAut_eq_inv_of_fixedPointFree {G : Type*} [Group G] [Finite G] (α : MulAut G)
    (hα : ∀ x, α (α x) = x) (hfix : ∀ x, α x = x → x = 1) : ∀ x, α x = x⁻¹ := by
  -- The map `u ↦ u⁻¹ * α u` is injective, hence surjective by finiteness.
  have hinj : Function.Injective (fun u : G => u⁻¹ * α u) := by
    intro x y hxy
    have h1 : y * x⁻¹ = α y * (α x)⁻¹ := by
      have := congrArg (fun t => y * t * (α x)⁻¹) hxy
      simpa [mul_assoc] using this
    have hz : α (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv, h1]
    have h2 : y * x⁻¹ = 1 := hfix (y * x⁻¹) hz
    exact (mul_inv_eq_one.mp h2).symm
  intro x
  obtain ⟨u, hu⟩ := (Finite.surjective_of_injective hinj) x
  -- x = u⁻¹ * α u lies in the image, and each such element is inverted by α.
  rw [← hu]
  rw [map_mul, map_inv, hα, mul_inv_rev, inv_inv]

end Work.BSLit.BenderFacts2.MyAux
