import Mathlib

namespace Work.LinnikBurgess

/-- Newton's identity for three reciprocal variables:
`∑ uᵢ⁻³ = (e₂(u)³ - 3 e₁(u) e₂(u) e₃(u) + 3 e₃(u)²) / e₃(u)³`. -/
lemma inv_pow_sum_three {k : Type*} [Field k] (u : Fin 3 → k) (hu : ∀ i, u i ≠ 0) :
    (∑ i : Fin 3, (u i)⁻¹ ^ 3)
      = ((u 0*u 1+u 0*u 2+u 1*u 2)^3
          - 3*(u 0+u 1+u 2)*(u 0*u 1+u 0*u 2+u 1*u 2)*(u 0*u 1*u 2)
          + 3*(u 0*u 1*u 2)^2) / (u 0*u 1*u 2)^3 := by
  have h0 := hu 0; have h1 := hu 1; have h2 := hu 2
  rw [Fin.sum_univ_three]
  field_simp
  ring

theorem powerSum_three_inv_eq_of_esymm_eq {k : Type*} [Field k]
    (a b : Fin 3 → k) (s : k)
    (he1 : a 0 + a 1 + a 2 = b 0 + b 1 + b 2)
    (he2 : a 0 * a 1 + a 0 * a 2 + a 1 * a 2 = b 0 * b 1 + b 0 * b 2 + b 1 * b 2)
    (he3 : a 0 * a 1 * a 2 = b 0 * b 1 * b 2)
    (hs : ∀ l : Fin 3, s + a l ≠ 0 ∧ s + b l ≠ 0) :
    (∑ l : Fin 3, ((s + a l)⁻¹) ^ 3) = (∑ l : Fin 3, ((s + b l)⁻¹) ^ 3) := by
  have ha : (∑ l : Fin 3, ((s + a l)⁻¹) ^ 3)
      = (((s + a 0)*(s + a 1)+(s + a 0)*(s + a 2)+(s + a 1)*(s + a 2))^3
         - 3*((s+a 0)+(s+a 1)+(s+a 2))*((s + a 0)*(s + a 1)+(s + a 0)*(s + a 2)+(s + a 1)*(s + a 2))*((s + a 0)*(s + a 1)*(s + a 2))
         + 3*((s + a 0)*(s + a 1)*(s + a 2))^2) / ((s + a 0)*(s + a 1)*(s + a 2))^3 := by
    simpa using inv_pow_sum_three (fun i => s + a i) (fun i => (hs i).1)
  have hb : (∑ l : Fin 3, ((s + b l)⁻¹) ^ 3)
      = (((s + b 0)*(s + b 1)+(s + b 0)*(s + b 2)+(s + b 1)*(s + b 2))^3
         - 3*((s+b 0)+(s+b 1)+(s+b 2))*((s + b 0)*(s + b 1)+(s + b 0)*(s + b 2)+(s + b 1)*(s + b 2))*((s + b 0)*(s + b 1)*(s + b 2))
         + 3*((s + b 0)*(s + b 1)*(s + b 2))^2) / ((s + b 0)*(s + b 1)*(s + b 2))^3 := by
    simpa using inv_pow_sum_three (fun i => s + b i) (fun i => (hs i).2)
  rw [ha, hb]
  have ha1 : (s + a 0) + (s + a 1) + (s + a 2) = 3*s + (a 0 + a 1 + a 2) := by ring
  have ha2 : (s + a 0)*(s + a 1) + (s + a 0)*(s + a 2) + (s + a 1)*(s + a 2) = 3*s^2 + 2*(a 0 + a 1 + a 2)*s + (a 0*a 1 + a 0*a 2 + a 1*a 2) := by ring
  have ha3 : (s + a 0)*(s + a 1)*(s + a 2) = s^3 + (a 0 + a 1 + a 2)*s^2 + (a 0*a 1 + a 0*a 2 + a 1*a 2)*s + a 0*a 1*a 2 := by ring
  have hb1 : (s + b 0) + (s + b 1) + (s + b 2) = 3*s + (b 0 + b 1 + b 2) := by ring
  have hb2 : (s + b 0)*(s + b 1) + (s + b 0)*(s + b 2) + (s + b 1)*(s + b 2) = 3*s^2 + 2*(b 0 + b 1 + b 2)*s + (b 0*b 1 + b 0*b 2 + b 1*b 2) := by ring
  have hb3 : (s + b 0)*(s + b 1)*(s + b 2) = s^3 + (b 0 + b 1 + b 2)*s^2 + (b 0*b 1 + b 0*b 2 + b 1*b 2)*s + b 0*b 1*b 2 := by ring
  rw [ha1, ha2, ha3, hb1, hb2, hb3, he1, he2, he3]

end Work.LinnikBurgess
