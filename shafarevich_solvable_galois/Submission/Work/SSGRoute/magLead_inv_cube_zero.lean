import Mathlib
import Submission.Work.SSGRoute.prop5.magnusGroupPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.SSGRoute.prop5

/-- The Magnus leading term of an inverse: if the cube of the leading term vanishes, then
`magLead N z⁻¹ = -magLead N z + (magLead N z)^2`. -/
theorem magLead_inv_cube_zero {X : Type*} (N : ℕ) (z : FreeGroup X)
    (h : (Work.SSGRoute.prop5.magLead N z) ^ 3 = 0) :
    Work.SSGRoute.prop5.magLead N (z⁻¹) =
      - Work.SSGRoute.prop5.magLead N z + (Work.SSGRoute.prop5.magLead N z) ^ 2 := by
  set a : FreeAssoc X ⧸ fil X N := magLead N z with ha
  set w : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N z with hw
  have haval : a = (w : FreeAssoc X ⧸ fil X N) - 1 := by rw [ha, hw]; rfl
  have hwval : (w : FreeAssoc X ⧸ fil X N) = 1 + a := by rw [haval]; noncomm_ring
  -- `h` has been rewritten by `set` into `a ^ 3 = 0`
  have hcube : a ^ 3 = 0 := h
  -- `(1 + a) * (1 - a + a^2) = 1 + a^3 = 1`
  have hpoly : (1 + a) * (1 - a + a ^ 2) = 1 + a ^ 3 := by noncomm_ring
  have hA : (w : FreeAssoc X ⧸ fil X N) * (1 - a + a ^ 2) = 1 := by
    rw [hwval, hpoly, hcube, add_zero]
  -- the unit `w` times its inverse is `1`
  have hwinv : ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
      * (w : FreeAssoc X ⧸ fil X N) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- hence `w⁻¹ = 1 - a + a^2`
  have hcalc : ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 - a + a ^ 2 := by
    calc ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
        = ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) * 1 := (mul_one _).symm
      _ = ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
            * ((w : FreeAssoc X ⧸ fil X N) * (1 - a + a ^ 2)) := by rw [hA]
      _ = (((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
            * (w : FreeAssoc X ⧸ fil X N)) * (1 - a + a ^ 2) := by rw [mul_assoc]
      _ = 1 * (1 - a + a ^ 2) := by rw [hwinv]
      _ = 1 - a + a ^ 2 := one_mul _
  -- `z⁻¹` has Magnus image `w⁻¹`
  have hgoal : Work.SSGRoute.prop5.magLead N (z⁻¹)
      = ((w⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 := by
    rw [magLead, map_inv, hw]
  rw [hgoal, hcalc]
  noncomm_ring

end Work.SSGRoute
