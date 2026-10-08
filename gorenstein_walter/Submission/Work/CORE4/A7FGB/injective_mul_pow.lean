import Mathlib

set_option linter.unusedVariables false

namespace Work.CORE4.A7FGB

/-- The elements `v * x` and `v * x ^ 2` (for `v` ranging over the non-identity
elements of an elementary abelian `2`-subgroup `V`) are all distinct, provided
`x` has order `3`.

Concretely: if `v₁ * x ^ a = v₂ * x ^ b` with `v₁, v₂ ∈ V ∖ {1}` and
`a, b ∈ {1, 2}`, then `v₁⁻¹ * v₂ = x ^ (a - b) ∈ V`, so `x ^ (2 (a - b)) = 1`
and hence `3 ∣ 2 (a - b)`, forcing `a = b` and then `v₁ = v₂`. -/
theorem injective_mul_pow {G : Type*} [Group G] (V : Subgroup G) (x : G)
    (hV2 : ∀ v ∈ V, v * v = 1) (hx3 : orderOf x = 3) (hcomm : ∀ v ∈ V, v * x = x * v) :
    Function.Injective (fun p : {v : ↥V // v ≠ 1} × Fin 2 =>
      (p.1.val : G) * x ^ (p.2.val + 1)) := by
  intro p q h
  obtain ⟨⟨v1, hv1⟩, i1⟩ := p
  obtain ⟨⟨v2, hv2⟩, i2⟩ := q
  simp only at h
  -- Move to integer exponents, where subtraction is available.
  have hz : (v1 : G) * x ^ (((i1.val + 1 : ℕ)) : ℤ) = (v2 : G) * x ^ (((i2.val + 1 : ℕ)) : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact h
  -- Isolate the quotient: `x ^ (a - b) = v₁⁻¹ * v₂`.
  have hmul : x ^ (((i1.val + 1 : ℕ)) : ℤ)
      = (v1 : G)⁻¹ * (v2 : G) * x ^ (((i2.val + 1 : ℕ)) : ℤ) := by
    calc x ^ (((i1.val + 1 : ℕ)) : ℤ) = (v1 : G)⁻¹ * ((v1 : G) * x ^ (((i1.val + 1 : ℕ)) : ℤ)) := by group
      _ = (v1 : G)⁻¹ * ((v2 : G) * x ^ (((i2.val + 1 : ℕ)) : ℤ)) := by rw [hz]
      _ = (v1 : G)⁻¹ * (v2 : G) * x ^ (((i2.val + 1 : ℕ)) : ℤ) := by group
  have hfinal : x ^ (((i1.val + 1 : ℕ)) : ℤ) * (x ^ (((i2.val + 1 : ℕ)) : ℤ))⁻¹ = (v1 : G)⁻¹ * (v2 : G) := by
    calc x ^ (((i1.val + 1 : ℕ)) : ℤ) * (x ^ (((i2.val + 1 : ℕ)) : ℤ))⁻¹
        = ((v1 : G)⁻¹ * (v2 : G) * x ^ (((i2.val + 1 : ℕ)) : ℤ)) * (x ^ (((i2.val + 1 : ℕ)) : ℤ))⁻¹ := by rw [hmul]
      _ = (v1 : G)⁻¹ * (v2 : G) := by group
  have hstep : (v1 : G)⁻¹ * (v2 : G)
      = x ^ ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) := by
    rw [zpow_sub]
    exact hfinal.symm
  -- Hence `x ^ (a - b) ∈ V`, and since `V` is elementary abelian, its square is `1`.
  have hxV : x ^ ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) ∈ V := by
    rw [← hstep]
    exact mul_mem (inv_mem v1.property) v2.property
  have hsq : x ^ ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ))
      * x ^ ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) = 1 := hV2 _ hxV
  have hpow : x ^ (2 * ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ))) = 1 := by
    rw [two_mul, zpow_add]
    exact hsq
  -- So `3 ∣ 2 (a - b)`, hence `3 ∣ (a - b)`, hence `a = b`.
  have hdvd2 : (3 : ℤ) ∣ 2 * ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) := by
    have hh : (orderOf x : ℤ) ∣ 2 * ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) := by
      rw [orderOf_dvd_iff_zpow_eq_one]; exact hpow
    simpa [hx3] using hh
  have hdvd : (3 : ℤ) ∣ ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ)) := by
    have hsub := dvd_sub (dvd_mul_right (3 : ℤ) ((((i1.val + 1 : ℕ)) : ℤ) - (((i2.val + 1 : ℕ)) : ℤ))) hdvd2
    convert hsub using 1
    ring
  have hdvdK : (3 : ℤ) ∣ ((i1.val : ℤ) - (i2.val : ℤ)) := by
    convert hdvd using 1
    push_cast
    ring
  have hi : i1 = i2 := by
    have h1 := i1.isLt
    have h2 := i2.isLt
    omega
  -- With `i1 = i2` the two powers coincide, and right cancellation gives `v₁ = v₂`.
  have hav : (v1 : G) = (v2 : G) := by
    rw [hi] at h
    exact mul_right_cancel h
  exact Prod.ext (Subtype.ext (Subtype.coe_injective hav)) hi

end Work.CORE4.A7FGB
