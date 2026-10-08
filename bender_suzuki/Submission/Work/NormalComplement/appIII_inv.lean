import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.NormalComplement

theorem appIII_inv {F : Type*} [Group F] {Q : Subgroup F} {u : F}
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hodd : Odd (Nat.card ↥Q))
    (hu : u * u = 1)
    (hnorm : ∀ x ∈ Q, u * x * u⁻¹ ∈ Q)
    (hfix : ∀ x ∈ Q, u * x * u⁻¹ = x → x = 1) :
    ∀ x ∈ Q, u * x * u⁻¹ = x⁻¹ := by
  intro x hx
  -- `u` is an involution
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  -- conjugation by `u` is multiplicative
  have mul_conj : ∀ a b : F, u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by
    intro a b; group
  -- conjugation by `u` is an involution on `F`
  have conj_conj : ∀ a : F, u * (u * a * u⁻¹) * u⁻¹ = a := by
    intro a
    have h : u * (u * a * u⁻¹) * u⁻¹ = (u * u) * a * (u⁻¹ * u⁻¹) := by group
    rw [h, hu, one_mul, hu_inv, hu, mul_one]
  -- `x * (u * x * u⁻¹)` is fixed by conjugation by `u`
  have hfy : u * (x * (u * x * u⁻¹)) * u⁻¹ = x * (u * x * u⁻¹) := by
    rw [mul_conj, conj_conj]
    exact hQab (u * x * u⁻¹) (hnorm x hx) x hx
  have hyQ : x * (u * x * u⁻¹) ∈ Q := Q.mul_mem hx (hnorm x hx)
  have h1 : x * (u * x * u⁻¹) = 1 := hfix _ hyQ hfy
  exact (mul_eq_one_iff_inv_eq.mp h1).symm

end Work.NormalComplement
