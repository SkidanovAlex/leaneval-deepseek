import Mathlib
import Submission.Work.BW.logHeight_prod_zpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- `exp (∑ᵢ cᵢ log wᵢ) = ∏ᵢ wᵢ^{cᵢ}` for nonzero `wᵢ` and integer exponents `cᵢ`. -/
lemma exp_sum_int_mul_log {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i, w i ≠ 0) (c : Fin n → ℤ) :
    Complex.exp (∑ i, (c i : ℂ) * Complex.log (w i)) = ∏ i, w i ^ c i := by
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, Complex.exp_log (hw i)]

/-- If `Complex.exp (2⁻ᵛ * ∑ᵢ Lᵢ log (φ (αᵢ))) = φ β` with all `αᵢ ≠ 0`, then the `2^v`-th
power of `β` is the monomial `∏ᵢ αᵢ^{Lᵢ}`: raising the hypothesis to the `2^v`-th power kills
the factor `2⁻ᵛ` and turns the exponential of the sum into the corresponding monomial. -/
lemma pow_eq_prod_of_exp {K : Type*} [Field K] (φ : K →+* ℂ) {n : ℕ} (α : Fin n → K)
    (hα : ∀ i, α i ≠ 0) (L : Fin n → ℤ) (v : ℕ) (β : K)
    (h : Complex.exp (((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))) = φ β) :
    β ^ (2 ^ v) = ∏ i, α i ^ (L i) := by
  have hφ : ∀ i, φ (α i) ≠ 0 := fun i h0 => hα i (φ.injective (by rw [h0, map_zero]))
  have hexp := exp_sum_int_mul_log (fun i => φ (α i)) hφ L
  have hmap : (∏ i, (φ (α i)) ^ (L i)) = φ (∏ i, α i ^ (L i)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => (map_zpow₀ φ (α i) (L i)).symm
  have hkey : Complex.exp (∑ i, (L i : ℂ) * Complex.log (φ (α i))) = (φ β) ^ (2 ^ v) := by
    have hne : ((2 : ℂ) ^ v) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hstep := Complex.exp_nat_mul
      (((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))) (2 ^ v)
    have hXV : ((2 ^ v : ℕ) : ℂ) * (((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i)))
        = ∑ i, (L i : ℂ) * Complex.log (φ (α i)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [hXV] at hstep
    rw [hstep, h]
  apply φ.injective
  rw [map_pow, ← hkey, hexp, hmap]

/-- Height bound for a `2^v`-th root of a monomial: if `β ^ 2^v = ∏ᵢ αᵢ^{Lᵢ}` then
`logHeight₁ β ≤ 2⁻ᵛ * ∑ᵢ |Lᵢ| * logHeight₁ (αᵢ)`. -/
lemma logHeight_le_of_pow_eq_prod {K : Type*} [Field K] [NumberField K] {n : ℕ} (α : Fin n → K)
    (L : Fin n → ℤ) (v : ℕ) (β : K) (h : β ^ (2 ^ v) = ∏ i, α i ^ (L i)) :
    Height.logHeight₁ β ≤
      (((2 : ℝ) ^ v)⁻¹) * ∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
  have h2v : Height.logHeight₁ (β ^ (2 ^ v)) = ((2 : ℝ) ^ v) * Height.logHeight₁ β := by
    rw [Height.logHeight₁_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hbound : ((2 : ℝ) ^ v) * Height.logHeight₁ β ≤
      ∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
    rw [← h2v, h]
    exact logHeight_prod_zpow_le α L
  have hpos : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hpos))
  rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at this

/-- Height bound for a `2^v`-th root of a monomial: if `Complex.exp (2⁻ᵛ * ∑ i, L i * log (φ (α i))) = φ β`
with all `α i ≠ 0`, then `logHeight₁ β ≤ 2⁻ᵛ * ∑ i, |L i| * logHeight₁ (α i)`. -/
theorem kummer_logHeight_le {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) {n : ℕ}
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (L : Fin n → ℤ) (v : ℕ) (β : K)
    (h : Complex.exp (((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))) = φ β) :
    Height.logHeight₁ β ≤ (((2 : ℝ) ^ v)⁻¹) * ∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
  exact logHeight_le_of_pow_eq_prod α L v β (pow_eq_prod_of_exp φ α hα L v β h)

end Work.BW
