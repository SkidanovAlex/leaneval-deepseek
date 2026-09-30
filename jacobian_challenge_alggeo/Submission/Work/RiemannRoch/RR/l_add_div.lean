import Mathlib
import Submission.Work.RiemannRoch.Pole

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Invariance of `l` under adding a principal divisor

For a curve `C` over a field `k`, a divisor `D` and a nonzero rational function `z`, the
Riemann-Roch spaces `L D` and `L (D + div z)` have the same dimension over `k`:

`l (D + div z) = l D`.

This is the elementary half of Riemann-Roch: multiplication by `z⁻¹` defines a `k`-linear
isomorphism `L D ≃ L (D + div z)`, since

`div (z⁻¹ * f) + (D + div z) = div f + D`.

The same statement is used in the blueprint (`NOTES_LEAD_jacobian_RR.md`, RR2.c) to shift
divisors by principal divisors.
-/

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

/-- Multiplication by `z ≠ 0` maps `L (D + div z)` onto `L D`. -/
theorem l_add_div {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (D : C.Div)
    {z : C.functionField} (hz : z ≠ 0) : C.l (D + C.div z) = C.l D := by
  -- Membership: `z * f ∈ L D` iff `f ∈ L (D + div z)`, because the two defining
  -- divisors are equal up to reordering of the summands.
  have hmul : ∀ f : C.functionField, z * f ∈ C.L D ↔ f ∈ C.L (D + C.div z) := by
    intro f
    rw [C.mem_L_iff, C.mem_L_iff]
    by_cases hf : f = 0
    · subst hf; simp
    · have hzf : z * f ≠ 0 := mul_ne_zero hz hf
      simp only [hf, hzf, false_or]
      rw [C.div_mul hz hf]
      exact iff_of_eq (congrArg _ (by abel))
  -- Consequently `LinearMap.mulLeft k z` maps `L (D + div z)` onto `L D`, and it is injective.
  have hmap : (C.L (D + C.div z)).map (LinearMap.mulLeft k z) = C.L D := by
    ext g
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hmul f).mpr hf
    · intro hg
      refine ⟨z⁻¹ * g, ?_, ?_⟩
      · have h2 : z * (z⁻¹ * g) ∈ C.L D := by rwa [mul_inv_cancel_left₀ hz g]
        exact (hmul (z⁻¹ * g)).mp h2
      · exact mul_inv_cancel_left₀ hz g
  have hinj : Function.Injective
      (LinearMap.mulLeft k z : C.functionField →ₗ[k] C.functionField) := by
    intro a b hab
    exact mul_left_cancel₀ hz (by simpa using hab)
  -- An injective linear map restricts to a linear equivalence onto the image, so the
  -- dimensions of `L (D + div z)` and of its image `L D` agree.
  calc C.l (D + C.div z)
      = Module.finrank k ((C.L (D + C.div z)).map
          (LinearMap.mulLeft k z : C.functionField →ₗ[k] C.functionField)) :=
        LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)
    _ = Module.finrank k (C.L D) := by rw [hmap]
    _ = C.l D := rfl

end Work.RiemannRoch.RR
