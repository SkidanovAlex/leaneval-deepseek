import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

open scoped commutatorElement

/-- If every square in a group `P` is central, then every commutator `⁅x, y⁆`
has order dividing two.

The key steps are: `(xy)² = ⁅x,y⁆ · x² · y²`, so `⁅x,y⁆` is a product of central
elements and hence central; and as `⁅x,y⁆` commutes with `x`, we have
`⁅x,y⁆² = ⁅x²,y⁆`, which is `1` because `x²` is central. -/
theorem commutator_sq_eq_one_of_sq_mem_center {P : Type} [Group P]
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (x y : P) : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
  have hx2 : x ^ 2 ∈ Subgroup.center P := hb x
  have hy2 : y ^ 2 ∈ Subgroup.center P := hb y
  have hxy2 : (x * y) ^ 2 ∈ Subgroup.center P := hb (x * y)
  have hxyx : y⁻¹ * x ^ 2 = x ^ 2 * y⁻¹ := (Subgroup.mem_center_iff.mp hx2) y⁻¹
  -- `⁅x,y⁆ * (x² * y²) = (x * y)²`
  have hkey : (x * y * x⁻¹ * y⁻¹) * (x ^ 2 * y ^ 2) = (x * y) ^ 2 := by
    calc (x * y * x⁻¹ * y⁻¹) * (x ^ 2 * y ^ 2)
        = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by group
      _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [hxyx]
      _ = (x * y) ^ 2 := by simp only [pow_two]; group
  have hmem : x ^ 2 * y ^ 2 ∈ Subgroup.center P := Subgroup.mul_mem _ hx2 hy2
  -- hence `⁅x,y⁆` is central, being `(x * y)² * (x² * y²)⁻¹`
  have hc : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P := by
    have hthis : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (x ^ 2 * y ^ 2)⁻¹ := by
      rw [← hkey]; group
    rw [hthis]
    exact Subgroup.mul_mem _ hxy2 (Subgroup.inv_mem _ hmem)
  have hcomm : Commute x (x * y * x⁻¹ * y⁻¹) := (Subgroup.mem_center_iff.mp hc) x
  have hcx : Commute (x ^ 2) y := ((Subgroup.mem_center_iff.mp hx2) y).symm
  show ⁅x, y⁆ ^ 2 = 1
  rw [hcomm.commutatorElement_pow_left 2, commutatorElement_eq_one_iff_commute.mpr hcx]

end Work.Higman
