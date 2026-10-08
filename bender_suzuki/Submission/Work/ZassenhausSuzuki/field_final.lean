import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem field_final {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1) {lam nu : K}
    (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) (hnu : nu = lam * lam / (1 + lam))
    (hrel : nu⁻¹ * θ nu⁻¹ = (lam⁻¹ * lam⁻¹) * θ (lam⁻¹ * lam⁻¹) + lam⁻¹ * θ (lam⁻¹)) : False := by
  -- In characteristic `2`, `1 + 1 = 0`.
  have h2 : (1:K) + 1 = 0 := by
    have h : (2:K) = 0 := CharP.cast_eq_zero (R := K) 2
    have hh : (1:K) + 1 = (2:K) := by norm_num
    rw [hh, h]
  -- Hence `1 + lam ≠ 0`, since it would force `lam = 1`.
  have h1l : (1:K) + lam ≠ 0 := by
    intro h
    apply hl1
    calc lam = 0 + lam := by ring
      _ = (1 + 1) + lam := by rw [h2]
      _ = 1 + (1 + lam) := by ring
      _ = 1 + 0 := by rw [h]
      _ = 1 := by ring
  have hθl : θ lam ≠ 0 := fun h => hl0 (θ.injective (by rw [h, map_zero]))
  have hθ1l : (1:K) + θ lam ≠ 0 := by
    intro h
    apply h1l
    apply θ.injective
    rw [map_add, map_one, h, map_zero]
  -- Inverse of `ν` on the two sides.
  have hA : nu⁻¹ = lam⁻¹ * lam⁻¹ + lam⁻¹ := by
    rw [hnu]; field_simp
  have hθnu : θ nu = θ lam * θ lam / (1 + θ lam) := by
    rw [hnu, map_div₀, map_mul, map_add, map_one]
  have hD : (θ nu)⁻¹ = (θ lam)⁻¹ * (θ lam)⁻¹ + (θ lam)⁻¹ := by
    rw [hθnu]; field_simp
  -- Substituting gives `(A² + A)(B² + B) = A²B² + AB` with `A = λ⁻¹`, `B = (θλ)⁻¹`,
  -- i.e. `A·B·(A + B) = 0`.
  have key : lam⁻¹ * (θ lam)⁻¹ * (lam⁻¹ + (θ lam)⁻¹) = 0 := by
    have hrel1 := hrel
    simp only [map_inv₀, map_mul] at hrel1
    rw [hA, hD] at hrel1
    linear_combination hrel1
  have hne : lam⁻¹ * (θ lam)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hl0) (inv_ne_zero hθl)
  have hsum : lam⁻¹ + (θ lam)⁻¹ = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · exact h
  -- In characteristic `2` this gives `λ⁻¹ = (θλ)⁻¹`, hence `λ = θλ`.
  have hAB : lam⁻¹ = (θ lam)⁻¹ := by
    have := eq_neg_of_add_eq_zero_left hsum
    rwa [CharTwo.neg_eq] at this
  have hlam : lam = θ lam := inv_inj.mp hAB
  rcases hfix lam hlam.symm with h | h
  · exact hl0 h
  · exact hl1 h

end Work.ZassenhausSuzuki
