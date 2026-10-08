import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Conic

/-- If `-1` is a square in a finite field of odd characteristic, the conic `a² + b² = 1` has
`q - 1` points.  Proof: with `i² = -1` and `i ≠ 0`, the map `(a,b) ↦ a + i*b` is a bijection from
the conic onto `Fˣ` (the inverse is `u ↦ ((u + u⁻¹)/2, (u - u⁻¹)/(2*i))`). -/
theorem ncard_conic_plus (F : Type*) [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h : ∃ i : F, i * i = -1) :
    {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard = Nat.card F - 1 := by
  obtain ⟨i, hi⟩ := h
  have hi0 : i ≠ 0 := by
    intro hh; rw [hh, mul_zero] at hi
    exact one_ne_zero (by rw [← neg_neg (1:F), ← hi, neg_zero])
  have h2i : (2:F)*i ≠ 0 := mul_ne_zero h2 hi0
  have hsquare : ∀ a b : F, (a+i*b)*(a-i*b) = a^2+b^2 := by
    intro a b
    have hii : i*i+1 = 0 := by rw [hi]; ring
    linear_combination (-(b^2)) * hii
  have key_plus : ∀ u : Fˣ, (((u:F)+(u:F)⁻¹)/2) + i*(((u:F)-(u:F)⁻¹)/(2*i)) = (u:F) := by
    intro u; field_simp; ring
  have key_minus : ∀ u : Fˣ, (((u:F)+(u:F)⁻¹)/2) - i*(((u:F)-(u:F)⁻¹)/(2*i)) = (u:F)⁻¹ := by
    intro u; field_simp; ring
  have key_mem : ∀ u : Fˣ, (((u:F)+(u:F)⁻¹)/2)^2 + (((u:F)-(u:F)⁻¹)/(2*i))^2 = 1 := by
    intro u
    rw [← hsquare]
    rw [key_plus, key_minus]
    simp
  let toUnit : ∀ (a b : F), a^2+b^2=1 → Fˣ :=
    fun a b hab => Units.mk (a+i*b) (a-i*b) (by rw [hsquare, hab]) (by rw [mul_comm, hsquare, hab])
  have coe_toUnit : ∀ (a b : F) (hab : a^2+b^2=1), (↑(toUnit a b hab) : F) = a + i*b := by
    intro a b hab; rfl
  have coe_inv_toUnit : ∀ (a b : F) (hab : a^2+b^2=1), (↑(toUnit a b hab)⁻¹ : F) = a - i*b := by
    intro a b hab
    show (↑((Units.mk (a+i*b) (a-i*b) _ _)⁻¹) : F) = a - i*b
    rw [Units.inv_mk]
  have psi_toUnit : ∀ (p : F×F) (hp : p.1^2+p.2^2=1),
      (((↑(toUnit p.1 p.2 hp) : F) + (↑(toUnit p.1 p.2 hp)⁻¹ : F))/2,
       ((↑(toUnit p.1 p.2 hp) : F) - (↑(toUnit p.1 p.2 hp)⁻¹ : F))/(2*i)) = p := by
    intro p hp
    rw [coe_toUnit p.1 p.2 hp, coe_inv_toUnit p.1 p.2 hp]
    ext <;> field_simp <;> ring
  have key : {p : F×F | p.1^2+p.2^2=1}.ncard = (Set.univ : Set Fˣ).ncard := by
    apply Set.ncard_congr (fun p hp => toUnit p.1 p.2 hp)
    · intro p hp; exact Set.mem_univ _
    · intro p q hp hq heq
      have e1 := psi_toUnit p hp
      have e2 := psi_toUnit q hq
      rw [← e1, ← e2, heq]
    · intro u hu
      use (((u:F)+(u:F)⁻¹)/2, ((u:F)-(u:F)⁻¹)/(2*i))
      use key_mem u
      exact Units.ext (key_plus u)
  rw [key, Set.ncard_univ, Nat.card_units]

end Work.L2F.Conic
