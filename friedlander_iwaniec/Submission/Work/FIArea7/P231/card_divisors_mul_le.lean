import Mathlib

namespace Work.FIArea7.P231

/-- The number of divisors of a product is at most the product of the numbers of
divisors of the factors.

The injection sends a divisor `e` of `a * b` to the pair `(gcd e a, e / gcd e a)`;
the second component divides `b` because `gcd (e / gcd e a) (a / gcd e a) = 1` and
`e / gcd e a ∣ (a / gcd e a) * b`. -/
theorem card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have key : ∀ e ∈ (a * b).divisors, e / e.gcd a ∣ b := by
    intro e he
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp he
    have hpos : 0 < e.gcd a :=
      Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left e a)
        (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero (mul_ne_zero ha hb)))
    have hstep : e.gcd a * (e / e.gcd a) ∣ e.gcd a * (a / e.gcd a * b) :=
      calc e.gcd a * (e / e.gcd a) = e := Nat.mul_div_cancel' (Nat.gcd_dvd_left e a)
        _ ∣ a * b := hdvd
        _ = e.gcd a * (a / e.gcd a * b) := by
              rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right e a)]
    have hdvd' : e / e.gcd a ∣ a / e.gcd a * b :=
      Nat.dvd_of_mul_dvd_mul_left hpos hstep
    exact (Nat.coprime_div_gcd_div_gcd (m := e) (n := a) hpos).dvd_of_dvd_mul_left hdvd'
  have hmain : (a * b).divisors.card ≤ (a.divisors ×ˢ b.divisors).card := by
    refine Finset.card_le_card_of_injOn (fun e => (e.gcd a, e / e.gcd a)) ?_ ?_
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_product]
      exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right e a, ha⟩,
             Nat.mem_divisors.mpr ⟨key e he, hb⟩⟩
    · intro e he e' he' heq
      simp only [Prod.mk.injEq] at heq
      calc e = e.gcd a * (e / e.gcd a) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left e a)).symm
        _ = e'.gcd a * (e' / e'.gcd a) := by rw [heq.2, heq.1]
        _ = e' := Nat.mul_div_cancel' (Nat.gcd_dvd_left e' a)
  rwa [Finset.card_product] at hmain

end Work.FIArea7.P231
