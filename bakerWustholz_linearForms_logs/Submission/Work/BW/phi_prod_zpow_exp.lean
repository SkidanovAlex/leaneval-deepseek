import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem phi_prod_zpow_exp {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (hα : ∀ i, α i ≠ 0) (ℓ : Fin n → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (y : Fin n → ℤ) :
    φ (∏ i, α i ^ y i) = Complex.exp (∑ i, (y i : ℂ) * ℓ i) := by
  have h1 : φ (∏ i, α i ^ y i) = ∏ i, Complex.exp ((y i : ℂ) * ℓ i) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, ← hℓ i]
    exact (Complex.exp_int_mul (ℓ i) (y i)).symm
  rw [h1, ← Complex.exp_sum]

end Work.BW
