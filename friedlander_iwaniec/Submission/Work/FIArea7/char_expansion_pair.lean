/-
# `Work.FIArea7.char_expansion_pair` — the character expansion (*FI* (16.11)/(16.15)/(17.10))

The finite-Fourier identity at the heart of *FI*'s §16: detecting the congruence
`z₁ ≡ ω z₂ (mod 4d)` by the multiplicative characters of `(ℤ[i]/4d)^*` turns the *pair* sum

  `Σ_ω w(ω) Σ_{x,y : π y = ω π x} β_x β̄_y ψ_x ψ̄_y`

into the `J(χ)|S_χ|²` sum of (17.10), where `J(χ) = Σ_ω w(ω)χ(ω)` and `S_χ = Σ_z β_z χ(π z) ψ_z`.

`G` is the (finite abelian) group of classes, `X` the set of Gaussian integers carrying the
coefficients, `π : X → G` the class map, `w(ω) = (ω|d)` the weight on the rational classes, and
`ψ(z) = (z/|z|)^k` the Grossencharacter.  Crucially `ψ` need **not** factor through `π` (the
argument of `z` is not a class-level datum), which is why the identity is stated for an arbitrary
`ψ : X → ℂ` — this is the form (17.10) consumes.

Compare `Work.FIArea7.omega_orthogonality`, the special case `X = G`, `π = id`, `ψ : G →* ℂˣ` with
`w` inversion-symmetric; the proof below is the same three-fold expansion and orthogonality
computation, with the `star (χ (π y)) = χ (π y)⁻¹` step (`star_char'`) doing the work.
-/
import Mathlib
import Submission.Work.FIArea7.omega_orthogonality

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.FIArea7

open scoped BigOperators

variable {G X : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]

/-- **(16.11)/(16.15)/(17.10) in complete generality.** -/
theorem char_expansion_pair (π : X → G) (w : G → ℂ) (β : X → ℂ) (ψ : X → ℂ) :
    (∑ ω : G, w ω * ∑ x : X, ∑ y : X,
        (if π y = ω * π x then β x * star (β y) * ψ x * star (ψ y) else 0))
      = (1 / (Fintype.card G : ℂ)) *
        ∑ χ : AddChar (Additive G) ℂ,
          (∑ ω : G, w ω * χ (Additive.ofMul ω)) *
            ((∑ z : X, β z * χ (Additive.ofMul (π z)) * ψ z) *
             star (∑ z : X, β z * χ (Additive.ofMul (π z)) * ψ z)) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- the condition `ω * (π x * (π y)⁻¹) = 1` is `π y = ω * π x`
  have hcond : ∀ (ω : G) (x y : X), (ω * (π x * (π y)⁻¹) = 1) ↔ (π y = ω * π x) := by
    intro ω x y
    constructor
    · intro h
      rw [← mul_assoc] at h
      exact (mul_inv_eq_one.mp h).symm
    · intro h
      have h1 : (ω * π x) * (π y)⁻¹ = 1 := mul_inv_eq_one.mpr h.symm
      rwa [mul_assoc] at h1
  -- Step 1: the squared modulus of `S_χ` is a double sum with the character of the ratio
  have hA : ∀ χ : AddChar (Additive G) ℂ,
      (∑ z : X, β z * χ (Additive.ofMul (π z)) * ψ z)
        * star (∑ z : X, β z * χ (Additive.ofMul (π z)) * ψ z)
      = ∑ x : X, ∑ y : X,
          (β x * star (β y) * ψ x * star (ψ y)) * χ (Additive.ofMul (π x * (π y)⁻¹)) := by
    intro χ
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have h1 : star (β y * χ (Additive.ofMul (π y)) * ψ y)
        = star (β y) * χ (Additive.ofMul (π y)⁻¹) * star (ψ y) := by
      have hb : star (β y * χ (Additive.ofMul (π y)) * ψ y)
          = star (ψ y) * χ (Additive.ofMul (π y)⁻¹) * star (β y) := by
        rw [show β y * χ (Additive.ofMul (π y)) * ψ y
              = β y * (χ (Additive.ofMul (π y)) * ψ y) from by ring,
            star_mul, star_mul, star_char']
      rw [hb]
      calc star (ψ y) * χ (Additive.ofMul (π y)⁻¹) * star (β y)
          = (χ (Additive.ofMul (π y)⁻¹) * star (ψ y)) * star (β y) := by
            rw [mul_comm (star (ψ y)) (χ (Additive.ofMul (π y)⁻¹))]
        _ = star (β y) * (χ (Additive.ofMul (π y)⁻¹) * star (ψ y)) :=
            mul_comm (χ (Additive.ofMul (π y)⁻¹) * star (ψ y)) (star (β y))
        _ = star (β y) * χ (Additive.ofMul (π y)⁻¹) * star (ψ y) := by
            simp only [mul_assoc]
    rw [h1]
    have h2 : χ (Additive.ofMul (π x)) * χ (Additive.ofMul (π y)⁻¹)
        = χ (Additive.ofMul (π x * (π y)⁻¹)) := by
      rw [ofMul_mul, AddChar.map_add_eq_mul]
    rw [← h2]
    ring
  -- Step 2: multiply by the `ω`-sum
  have hB : ∀ χ : AddChar (Additive G) ℂ,
      (∑ ω : G, w ω * χ (Additive.ofMul ω)) *
        (∑ x : X, ∑ y : X,
          (β x * star (β y) * ψ x * star (ψ y)) * χ (Additive.ofMul (π x * (π y)⁻¹)))
      = ∑ ω : G, ∑ x : X, ∑ y : X,
          (w ω * (β x * star (β y) * ψ x * star (ψ y)))
            * χ (Additive.ofMul (ω * (π x * (π y)⁻¹))) := by
    intro χ
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ =>
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [ofMul_mul, AddChar.map_add_eq_mul]
    ring
  -- Step 3: sum over the characters and use orthogonality
  have hC : (∑ χ : AddChar (Additive G) ℂ, ∑ ω : G, ∑ x : X, ∑ y : X,
        (w ω * (β x * star (β y) * ψ x * star (ψ y)))
          * χ (Additive.ofMul (ω * (π x * (π y)⁻¹))))
      = (Fintype.card G : ℂ) * ∑ ω : G, ∑ x : X, ∑ y : X,
          (if π y = ω * π x then w ω * (β x * star (β y) * ψ x * star (ψ y)) else 0) := by
    rw [sum4_comm (fun (χ : AddChar (Additive G) ℂ) (ω : G) (x y : X) =>
      (w ω * (β x * star (β y) * ψ x * star (ψ y)))
        * χ (Additive.ofMul (ω * (π x * (π y)⁻¹))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, sum_char_ite']
    have hiff : (ω * (π x * (π y)⁻¹) = 1) ↔ (π y = ω * π x) := hcond ω x y
    by_cases h : π y = ω * π x
    · rw [if_pos h, if_pos (hiff.mpr h)]
      ring
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
      ring
  -- Step 4: assemble
  have hL : (∑ ω : G, w ω * ∑ x : X, ∑ y : X,
        (if π y = ω * π x then β x * star (β y) * ψ x * star (ψ y) else 0))
      = ∑ ω : G, ∑ x : X, ∑ y : X,
        (if π y = ω * π x then w ω * (β x * star (β y) * ψ x * star (ψ y)) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : π y = ω * π x <;> simp [h]
  rw [hL]
  simp only [hA, hB]
  rw [hC]
  rw [one_div, inv_mul_cancel_left₀ hcard]

end Work.FIArea7
