import Mathlib

namespace Work.HP.LatRecurse

/-- Over `ℤ`, the kernel of a surjective linear functional on `ℤ^R` has rank `R - 1`. -/
theorem ker_finrank {R : ℕ} (f : (Fin R → ℤ) →ₗ[ℤ] ℤ) (hf : Function.Surjective f) :
    Module.finrank ℤ (LinearMap.ker f) + 1 = R := by
  -- Rank–nullity for the quotient by the kernel, over the domain `ℤ`.
  have h1 := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := Fin R → ℤ) (LinearMap.ker f)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  -- The quotient by the kernel is isomorphic to the range, which is everything.
  have h2 : Module.finrank ℤ ((Fin R → ℤ) ⧸ LinearMap.ker f) = 1 := by
    rw [← Module.finrank_self ℤ]
    exact LinearEquiv.finrank_eq (LinearMap.quotKerEquivOfSurjective f hf)
  omega

end Work.HP.LatRecurse
