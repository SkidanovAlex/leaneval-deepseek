import Mathlib

/-!
# Character orthogonality for the weighted three-fold Fourier expansion

This file proves `Work.FIArea7.omega_orthogonality`, the orthogonality identity used in
Area 7 of the Friedlander--Iwaniec development: for a finite abelian group `G`, a weight
`w` invariant under inversion, and a character `ψ : G →* ℂˣ` of unit modulus, the
double-convolution-type sum

`∑ ω, w ω * ψ ω * ∑ y, β (ω*y) * star (β y)`

equals the normalised sum over all additive characters `χ` of
`(∑ ω, w ω * χ ω) * |∑ z, β z * χ z * ψ z|²`.

The proof expands the character sum into a three-fold sum over `𝔾`, swaps the order of
summation, applies the orthogonality relation `∑ χ, χ a = |G| [a = 1]`, and finally
re-indexes the resulting double sum.
-/

namespace Work.FIArea7

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ## Basic character facts -/

/-- `star` of a complex character value is the inverse, i.e. the value at the inverse
group element. -/
lemma star_char' (χ : AddChar (Additive G) ℂ) (x : G) :
    star (χ (Additive.ofMul x)) = χ (Additive.ofMul x⁻¹) := by
  rw [ofMul_inv, AddChar.map_neg_eq_inv]
  exact (AddChar.inv_apply_eq_conj χ (Additive.ofMul x)).symm

/-- Orthogonality of additive characters of a finite abelian group, in multiplicative form. -/
lemma sum_char_ite' (a : G) :
    (∑ χ : AddChar (Additive G) ℂ, χ (Additive.ofMul a))
      = if a = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [AddChar.sum_apply_eq_ite]
  simp only [ofMul_eq_zero]
  rw [← Fintype.card_congr Additive.ofMul]

/-! ## Reordering multiple finite sums -/

lemma sum3_comm {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]

lemma sum4_comm {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  exact sum3_comm (fun a c d => f a b c d)

/-! ## The three-fold character sum -/

/-- The core orthogonality computation: summing over all characters of the product of
the Fourier coefficient of `u` with the squared modulus of the Fourier coefficient of `v`. -/
lemma three_fold_char (u v : G → ℂ) :
    (∑ χ : AddChar (Additive G) ℂ,
       (∑ x, u x * χ (Additive.ofMul x))
         * ((∑ y, v y * χ (Additive.ofMul y)) * star (∑ y, v y * χ (Additive.ofMul y))))
    = (Fintype.card G : ℂ) * ∑ x, ∑ y, u x * v y * star (v (x*y)) := by
  simp_rw [← mul_assoc]
  have hexp : ∀ χ : AddChar (Additive G) ℂ,
      (∑ x, u x * χ (Additive.ofMul x)) * (∑ y, v y * χ (Additive.ofMul y))
         * star (∑ y, v y * χ (Additive.ofMul y))
      = ∑ x, ∑ y, ∑ z, u x * v y * star (v z) * χ (Additive.ofMul (x*y*z⁻¹)) := by
    intro χ
    have hstar : star (∑ y, v y * χ (Additive.ofMul y))
        = ∑ y, star (v y) * χ (Additive.ofMul y⁻¹) := by
      rw [star_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [star_mul, star_char']; ring
    rw [hstar, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _
    have hcm : χ (Additive.ofMul (x*y*z⁻¹))
        = χ (Additive.ofMul x) * χ (Additive.ofMul y) * χ (Additive.ofMul z⁻¹) := by
      rw [ofMul_mul, ofMul_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    rw [hcm]; ring
  simp_rw [hexp]
  rw [sum4_comm]
  have hinner : ∀ x y : G,
      (∑ z, ∑ χ : AddChar (Additive G) ℂ,
          u x * v y * star (v z) * χ (Additive.ofMul (x*y*z⁻¹)))
      = (Fintype.card G : ℂ) * (u x * v y * star (v (x*y))) := by
    intro x y
    have h1 : ∀ z : G, (∑ χ : AddChar (Additive G) ℂ,
          u x * v y * star (v z) * χ (Additive.ofMul (x*y*z⁻¹)))
        = (u x * v y * star (v z)) * (if x*y*z⁻¹ = 1 then (Fintype.card G : ℂ) else 0) := by
      intro z
      rw [← Finset.mul_sum, sum_char_ite']
    simp_rw [h1]
    have hc : ∀ z : G, (x*y*z⁻¹ = 1) ↔ (z = x*y) := by
      intro z; rw [mul_inv_eq_one, eq_comm]
    simp only [hc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [mul_comm]
  simp_rw [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]

/-! ## Re-indexing the resulting double sum -/

/-- Re-indexing step: the double sum produced by `three_fold_char` equals the original
(single-indexed) convolution expression. -/
lemma final_reindex (w : G → ℂ) (hw : ∀ ω : G, w ω⁻¹ = w ω) (ψ : G →* ℂˣ)
    (hψ : ∀ z : G, star ((ψ z : ℂ)) = ((ψ z : ℂ))⁻¹) (β : G → ℂ) :
    (∑ x, ∑ y, (w x * (β y * (ψ y : ℂ))) * star (β (x*y) * (ψ (x*y) : ℂ)))
    = (∑ ω, w ω * (ψ ω : ℂ) * ∑ y, β (ω * y) * star (β y)) := by
  have hA : ∀ x y : G, (w x * (β y * (ψ y : ℂ))) * star (β (x*y) * (ψ (x*y) : ℂ))
      = w x * ((ψ x : ℂ))⁻¹ * (β y * star (β (x*y))) := by
    intro x y
    have hmul : (ψ (x*y) : ℂ) = (ψ x : ℂ) * (ψ y : ℂ) := by rw [map_mul, Units.val_mul]
    have hstar : star (β (x*y) * (ψ (x*y) : ℂ))
        = ((ψ x : ℂ))⁻¹ * ((ψ y : ℂ))⁻¹ * star (β (x*y)) := by
      rw [hmul, star_mul, star_mul, hψ x, hψ y]
      ring
    rw [hstar]
    field_simp
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hA x y))]
  have hB : ∀ x : G, (∑ y, w x * ((ψ x : ℂ))⁻¹ * (β y * star (β (x*y))))
      = ∑ t, w x * ((ψ x : ℂ))⁻¹ * (β (x⁻¹ * t) * star (β t)) := by
    intro x
    rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)
        (fun y => w x * ((ψ x : ℂ))⁻¹ * (β y * star (β (x*y))))]
    apply Finset.sum_congr rfl; intro i _
    simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
  rw [Finset.sum_congr rfl (fun x _ => hB x)]
  have hD : (∑ ω, w ω * (ψ ω : ℂ) * ∑ y, β (ω * y) * star (β y))
      = ∑ ω, ∑ y, w ω * (ψ ω : ℂ) * (β (ω * y) * star (β y)) := by
    apply Finset.sum_congr rfl; intro ω _
    rw [Finset.mul_sum]
  rw [hD]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.inv G)
      (fun x => ∑ t, w x * ((ψ x : ℂ))⁻¹ * (β (x⁻¹ * t) * star (β t)))]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro t _
  simp only [Equiv.inv_apply, hw, inv_inv, map_inv, Units.val_inv_eq_inv_val]

/-! ## The target theorem -/

theorem omega_orthogonality {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (w : G → ℂ) (hw : ∀ ω : G, w ω⁻¹ = w ω)
    (ψ : G →* ℂˣ) (hψ : ∀ z : G, star ((ψ z : ℂ)) = ((ψ z : ℂ))⁻¹) (β : G → ℂ) :
    (∑ ω : G, w ω * (ψ ω : ℂ) * ∑ y : G, β (ω * y) * star (β y))
      = (1 / (Fintype.card G : ℂ)) *
        ∑ χ : AddChar (Additive G) ℂ,
          (∑ ω : G, w ω * χ (Additive.ofMul ω)) *
            ((∑ z : G, β z * χ (Additive.ofMul z) * (ψ z : ℂ)) *
              star (∑ z : G, β z * χ (Additive.ofMul z) * (ψ z : ℂ))) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBχ : ∀ χ : AddChar (Additive G) ℂ,
      (∑ z : G, β z * χ (Additive.ofMul z) * (ψ z : ℂ))
        = (∑ z : G, (β z * (ψ z : ℂ)) * χ (Additive.ofMul z)) := by
    intro χ
    apply Finset.sum_congr rfl; intro z _
    ring
  simp_rw [hBχ]
  rw [three_fold_char w (fun z => β z * (ψ z : ℂ))]
  rw [one_div, inv_mul_cancel_left₀ hcard]
  exact (final_reindex w hw ψ hψ β).symm

end Work.FIArea7
