import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- In a group where every square is central, the inverse of `(xy)^2` times `x^2 y^2`
equals the inverse of the commutator `x y x⁻¹ y⁻¹`.

The key identity is `(x*y)^2 = (x*y*x⁻¹*y⁻¹) * (x^2*y^2)`: it follows from
`y*x = (y*x*y⁻¹*x⁻¹)*(x*y)` and from centrality of `x^2`, which lets us move `x^2`
past `y⁻¹`.  Then the centrality of `(x*y)^2` (itself a square) does the rest. -/
theorem inv_sq_mul_sq_eq_commutator_inv {P : Type} [Group P]
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (x y : P) :
    ((x*y)^2)⁻¹ * (x^2 * y^2) = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
  have hxc : x^2 ∈ Subgroup.center P := hb x
  have hc : (x*y)^2 ∈ Subgroup.center P := hb (x*y)
  have hx2comm : ∀ z : P, z * x^2 = x^2 * z := fun z => (Subgroup.mem_center_iff.mp hxc) z
  -- Central identity: `(x*y)^2 = [x,y] * (x^2 * y^2)`.
  have hkey : (x*y)^2 = (x*y*x⁻¹*y⁻¹) * (x^2 * y^2) := by
    -- `y*x = (y*x*y⁻¹*x⁻¹)*(x*y)` is a pure group identity.
    have hyx : y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
    -- Using centrality of `x^2`, we may move the factor `x^2` across `y⁻¹`.
    have hEq : x * (y*x*y⁻¹*x⁻¹) * x = (x*y*x⁻¹*y⁻¹) * x^2 := by
      rw [show (x*y*x⁻¹*y⁻¹) * x^2 = (x*y*x⁻¹) * (y⁻¹ * x^2) by group]
      rw [hx2comm y⁻¹]
      group
    calc (x*y)^2 = x * (y*x) * y := by rw [pow_two]; group
      _ = x * ((y*x*y⁻¹*x⁻¹)*(x*y)) * y := by nth_rewrite 1 [hyx]; rfl
      _ = (x * (y*x*y⁻¹*x⁻¹) * x) * y^2 := by group
      _ = ((x*y*x⁻¹*y⁻¹) * x^2) * y^2 := by rw [hEq]
      _ = (x*y*x⁻¹*y⁻¹) * (x^2 * y^2) := by group
  -- Rewrite the commutator as `(x*y)^2 * (x^2*y^2)⁻¹`, then commute using centrality.
  have hk : (x*y*x⁻¹*y⁻¹) = (x*y)^2 * (x^2*y^2)⁻¹ := by rw [hkey]; group
  rw [hk, mul_inv_rev, inv_inv]
  have hcinv : ((x*y)^2)⁻¹ ∈ Subgroup.center P := Subgroup.inv_mem _ hc
  exact ((Subgroup.mem_center_iff.mp hcinv) (x^2*y^2)).symm

end Work.Higman
