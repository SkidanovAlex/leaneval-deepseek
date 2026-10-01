import Mathlib

namespace Work.LinnikAreas.Density4

open Finset

/-- The summand `τ(e)/√e` is multiplicative on coprime arguments: for coprime `a`, `b`,
`τ(ab)/√(ab) = (τ(a)/√a) * (τ(b)/√b)`. -/
lemma tau_sqrtrecip_mul {a b : ℕ} (hab : a.Coprime b) :
    (((a * b).divisors.card : ℝ) / Real.sqrt ((a * b : ℕ) : ℝ))
      = ((a.divisors.card : ℝ) / Real.sqrt (a : ℝ))
        * ((b.divisors.card : ℝ) / Real.sqrt (b : ℝ)) := by
  rw [Nat.Coprime.card_divisors_mul hab]
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg a)]
  rw [mul_div_mul_comm]

/-- For coprime `m`, `n` the divisors of `m * n` are exactly the products `a * b` with
`a ∣ m`, `b ∣ n`, each occurring once. -/
lemma divisors_mul_coprime_image {m n : ℕ} (hmn : m.Coprime n) :
    (m * n).divisors = (m.divisors ×ˢ n.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) := by
  rw [hmn.divisors_mul, Finset.map_eq_image]
  conv_rhs => rw [← Finset.attach_image_val (s := m.divisors ×ˢ n.divisors)]
  rw [Finset.image_image]
  rfl

/-- The divisor sum `∑_{e ∣ n} τ(e)/√e` is multiplicative over coprime factors. -/
theorem divisors_tau_sqrtrecip_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    (∑ e ∈ (m * n).divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ))
      = (∑ e ∈ m.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ))
        * ∑ e ∈ n.divisors, (e.divisors.card : ℝ) / Real.sqrt (e : ℝ) := by
  rw [divisors_mul_coprime_image hmn, Finset.sum_image (Nat.Coprime.mul_injOn_divisors hmn),
    Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha1, _⟩ := Nat.mem_divisors.mp ha
  obtain ⟨hb1, _⟩ := Nat.mem_divisors.mp hb
  exact tau_sqrtrecip_mul
    (Nat.Coprime.coprime_dvd_right hb1 (Nat.Coprime.coprime_dvd_left ha1 hmn))

end Work.LinnikAreas.Density4
