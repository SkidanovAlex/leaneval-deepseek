import Mathlib

namespace Work.LinnikAreas.Density4

/-- The divisor sum `∑_{d ∣ n} 1/√d` is multiplicative over coprime factors. -/
theorem divisors_sqrtrecip_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    (∑ d ∈ (m * n).divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      = (∑ d ∈ m.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
        * ∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ) := by
  -- For coprime `m, n`, multiplication is injective on `divisors m × divisors n`.
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors) := by
    intro p hp q hq hpq
    change p.1 * p.2 = q.1 * q.2 at hpq
    simp only [Finset.mem_product, Finset.mem_coe] at hp hq
    obtain ⟨hpa, hpb⟩ := hp
    obtain ⟨hqa, hqb⟩ := hq
    have hpapos : 0 < p.1 := Nat.pos_of_mem_divisors hpa
    have hpdvd : p.1 ∣ m := (Nat.mem_divisors.mp hpa).1
    have hqdvd : q.1 ∣ m := (Nat.mem_divisors.mp hqa).1
    have hpdvdn : p.2 ∣ n := (Nat.mem_divisors.mp hpb).1
    have hqdvdn : q.2 ∣ n := (Nat.mem_divisors.mp hqb).1
    -- `p.1` divides `m` and `q.2` divides `n`, which are coprime.
    have hcp1 : p.1.Coprime q.2 := (hmn.coprime_dvd_right hqdvdn).coprime_dvd_left hpdvd
    have hcp2 : q.1.Coprime p.2 := (hmn.coprime_dvd_right hpdvdn).coprime_dvd_left hqdvd
    have hpdvd2 : p.1 ∣ q.1 := hcp1.dvd_of_dvd_mul_right (by rw [← hpq]; exact dvd_mul_right _ _)
    have hqdvd2 : q.1 ∣ p.1 := hcp2.dvd_of_dvd_mul_right (by rw [hpq]; exact dvd_mul_right _ _)
    have hap : p.1 = q.1 := Nat.dvd_antisymm hpdvd2 hqdvd2
    have hbp : p.2 = q.2 := Nat.mul_left_cancel hpapos (by rw [hpq, ← hap])
    exact Prod.ext hap hbp
  rw [Nat.divisors_mul, Finset.mul_def]
  rw [Finset.sum_image hinj]
  rw [Finset.sum_product]
  -- `1/√(a·b) = 1/√a · 1/√b`.
  have hmul : ∀ a b : ℕ,
      (1 : ℝ) / Real.sqrt ((a * b : ℕ) : ℝ)
        = (1 : ℝ) / Real.sqrt (a : ℝ) * ((1 : ℝ) / Real.sqrt (b : ℝ)) := by
    intro a b
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a), one_div_mul_one_div]
  simp only [hmul]
  rw [← Finset.sum_mul_sum]

end Work.LinnikAreas.Density4
