import Mathlib

namespace NK.LocalCFT.Units

/-- If every element of a finite group `G` satisfies `x ^ n = 1`, then every prime `q` dividing
the order of `G` divides `n`.  Indeed, by Cauchy's theorem `q ∣ Nat.card G` yields an element `x`
of order `q`, and `x ^ n = 1` gives `orderOf x ∣ n`, i.e. `q ∣ n`. -/
theorem prime_dvd_natCard_of_pow_eq_one {G : Type*} [Group G] [Finite G] {n q : ℕ}
    (h : ∀ x : G, x ^ n = 1) (hq : q.Prime) (hdvd : q ∣ Nat.card G) : q ∣ n := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q (hp := Fact.mk hq) hdvd
  rw [← hx]
  exact orderOf_dvd_of_pow_eq_one (h x)

end NK.LocalCFT.Units
