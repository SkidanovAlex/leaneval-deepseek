import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FineCoords

theorem bilinear_invariant_eq {F : Type*} [Field F] [CharP F 2] [Finite F]
    (φ : F → F → F)
    (hadd₁ : ∀ a b c : F, φ (a + b) c = φ a c + φ b c)
    (hadd₂ : ∀ a b c : F, φ a (b + c) = φ a b + φ a c)
    (hinv : ∀ t a b : F, φ (t * a) (t * b) = t ^ 2 * φ a b) :
    ∀ a b : F, φ a b = φ 1 1 * (a * b) := by
  -- Cross relation: scaling the first argument can be moved to the second one.
  -- Expand `hinv` at `t + 1`; in char 2 we have `(t+1)^2 = t^2 + 1`, so the
  -- `t^2 · φ a b` terms cancel and only the mixed terms survive.
  have hcross : ∀ t x y : F, φ (t * x) y = φ x (t * y) := by
    intro t x y
    have h := hinv (t + 1) x y
    rw [add_mul, one_mul, add_mul, one_mul] at h
    rw [hadd₁ (t * x) x (t * y + y)] at h
    rw [hadd₂ (t * x) (t * y) y, hadd₂ x (t * y) y] at h
    rw [hinv t x y] at h
    rw [CharTwo.add_sq, one_pow, add_mul, one_mul] at h
    have h2 : φ (t * x) y + φ x (t * y) = 0 := by linear_combination h
    have h3 : φ (t * x) y = - φ x (t * y) := eq_neg_of_add_eq_zero_left h2
    rwa [CharTwo.neg_eq] at h3
  -- Consequence: `φ a b` only depends on the product `a * b`.
  have h1 : ∀ a b : F, φ a b = φ 1 (a * b) := by
    intro a b
    simpa using hcross a 1 b
  -- The additive map `z ↦ φ 1 z` is homogeneous for squares.
  have hhom : ∀ t z : F, φ 1 (t ^ 2 * z) = t ^ 2 * φ 1 z := by
    intro t z
    have h2 := hinv t 1 z
    rw [mul_one] at h2
    have hc := hcross t 1 (t * z)
    rw [mul_one] at hc
    rw [show t ^ 2 * z = t * (t * z) by ring, ← hc, h2]
  -- In a finite field of characteristic 2, squaring is onto.
  have hsurj : Function.Surjective (fun t : F => t^2) := by
    apply Finite.surjective_of_injective
    intro a b hab
    change a^2 = b^2 at hab
    have h : (a + b)^2 = 0 := by
      rw [CharTwo.add_sq, hab]; rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
    have hz : a + b = 0 := sq_eq_zero_iff.mp h
    have : a = -b := eq_neg_of_add_eq_zero_left hz
    rwa [CharTwo.neg_eq] at this
  intro a b
  rw [h1 a b]
  obtain ⟨t, ht⟩ := hsurj (a * b)
  have hh := hhom t 1
  rw [mul_one] at hh
  rw [← ht, hh]
  ring

end Work.PSU3.FineCoords
