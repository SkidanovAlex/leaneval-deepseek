import Mathlib

/-!
# Plancherel for the character table of a finite abelian group

This file proves `Work.FIArea7.sum_normSq_fourier_mul`, the Plancherel (Parseval) identity for
the character table of a finite commutative group `G`, written multiplicatively:

  `∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (p)‖ ^ 2 = |G| * ∑ p, ‖a p‖ ^ 2`.

The proof follows the usual argument.  Expanding the squared modulus as
`F χ * star (F χ)`, distributing the two finite sums and swapping the order of summation,
the character sum collapses by the orthogonality relation

  `∑ χ, χ z * star (χ w) = |G| if z = w, and 0 otherwise`,

which is the multiplicative-content form of `AddChar.sum_apply_eq_ite` together with
`AddChar.inv_apply_eq_conj` (the fact that `star (χ x) = χ x⁻¹` because character values
have modulus one).
-/

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- `star` of a complex valued additive character at a group element is its value at the
inverse element: additive characters take values of modulus one, so conjugation inverts. -/
private lemma fi_star_addChar {G : Type*} [CommGroup G] [Fintype G]
    (χ : AddChar (Additive G) ℂ) (x : G) :
    star (χ (Additive.ofMul x)) = χ (Additive.ofMul x⁻¹) := by
  rw [ofMul_inv, AddChar.map_neg_eq_inv]
  exact (AddChar.inv_apply_eq_conj χ (Additive.ofMul x)).symm

/-- Orthogonality of the character table of a finite commutative group, written with `star` in
place of complex conjugation. -/
private lemma fi_sum_addChar_mul_star {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (z w : G) :
    (∑ χ : AddChar (Additive G) ℂ, χ (Additive.ofMul z) * star (χ (Additive.ofMul w)))
      = if z = w then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ χ : AddChar (Additive G) ℂ,
      χ (Additive.ofMul z) * star (χ (Additive.ofMul w))
        = χ (Additive.ofMul (z * w⁻¹)) := by
    intro χ
    rw [fi_star_addChar χ w, ← AddChar.map_add_eq_mul, ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  simp only [ofMul_eq_zero, mul_inv_eq_one, Fintype.card_additive]

/-- Reordering of a threefold finite sum. -/
private lemma fi_sum3_comm {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- Plancherel for the character table, in the `ℂ`-valued form in which the squared modulus is
written as `F χ * star (F χ)`. -/
private lemma fi_sum_char_mul_conj {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (a : G → ℂ) :
    ∑ χ : AddChar (Additive G) ℂ,
        (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p))
      = (Fintype.card G : ℂ) * ∑ p, a p * star (a p) := by
  classical
  have hexp : ∀ χ : AddChar (Additive G) ℂ,
      (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p))
        = ∑ p, ∑ q, (a p * star (a q)) *
            (χ (Additive.ofMul p) * star (χ (Additive.ofMul q))) := by
    intro χ
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul]
    ring
  simp_rw [hexp]
  rw [fi_sum3_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hinner : ∀ q : G,
      (∑ χ : AddChar (Additive G) ℂ,
          (a p * star (a q)) * (χ (Additive.ofMul p) * star (χ (Additive.ofMul q))))
        = (a p * star (a q)) * (if p = q then (Fintype.card G : ℂ) else 0) := by
    intro q
    rw [← Finset.mul_sum, fi_sum_addChar_mul_star]
  simp_rw [hinner]
  have hsingle : (∑ q, (a p * star (a q)) * (if p = q then (Fintype.card G : ℂ) else 0))
      = (a p * star (a p)) * (Fintype.card G : ℂ) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [if_neg (Ne.symm hq), mul_zero]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  rw [hsingle, mul_comm]

/-- `z * star z` is the real number `‖z‖ ^ 2`, transported to `ℂ`. -/
private lemma fi_mul_conj_eq_ofReal_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Plancherel for the character table of a finite abelian group, in the form needed for the §17
character sums: the `χ`-sum of the squared modulus of the Fourier transform of `a` is `|G|` times
the `L²`-mass of `a`. -/
theorem sum_normSq_fourier_mul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (a : G → ℂ) :
    ∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖ ^ 2
      = (Fintype.card G : ℝ) * ∑ p, ‖a p‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  have hpt : ∀ χ : AddChar (Additive G) ℂ,
      ((‖∑ p, a p * χ (Additive.ofMul p)‖ ^ 2 : ℝ) : ℂ)
        = (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p)) := by
    intro χ
    rw [fi_mul_conj_eq_ofReal_normSq]
  simp_rw [hpt]
  rw [fi_sum_char_mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp_rw [fi_mul_conj_eq_ofReal_normSq]

end Work.FIArea7
