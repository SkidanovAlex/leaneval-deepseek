import Mathlib

namespace Work.FIArea7

/-- Double counting: summing a function of the divisor pair `(b, n / b)` over all
`n ≤ X` and all divisors `b ∣ n` of `n` is the same as summing `H b m` over all
pairs `(b, m)` with `b * m ≤ X`.  The bijection is `(n, b) ↦ (b, n / b)` with
inverse `(b, m) ↦ (b * m, b)`. -/
theorem sum_divisors_eq_sum_prod_le (X : ℕ) (H : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ b ∈ n.divisors, H b (n / b))
      = ∑ b ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
          (if b * m ≤ X then H b m else 0) := by
  -- Turn the left-hand side into a sum over the sigma-type of pairs `(n, b)` with `b ∣ n`.
  rw [Finset.sum_sigma']
  -- Turn the right-hand side into a sum over pairs `(b, m)` satisfying `b * m ≤ X`.
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter (fun x : ℕ × ℕ => x.1 * x.2 ≤ X) (fun x => H x.1 x.2)]
  -- Reindex by the bijection `(n, b) ↦ (b, n / b)`, inverse `(b, m) ↦ (b * m, b)`.
  refine Finset.sum_nbij' (fun a => (a.snd, a.fst / a.snd))
    (fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · -- `(b, n / b)` lies in the target set for `b ∈ n.divisors`, `n ∈ Icc 1 X`.
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp ha1
    obtain ⟨hbdvd, _⟩ := Nat.mem_divisors.mp ha2
    have hbpos : 0 < a.snd := Nat.pos_of_dvd_of_pos hbdvd (show 0 < a.fst by omega)
    have hble : a.snd ≤ a.fst := Nat.le_of_dvd (show 0 < a.fst by omega) hbdvd
    have hdivpos : 0 < a.fst / a.snd := Nat.div_pos hble hbpos
    have hdivle : a.fst / a.snd ≤ X := le_trans (Nat.div_le_self a.fst a.snd) hnX
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      by rw [Nat.mul_div_cancel' hbdvd]; omega⟩
  · -- `(b * m, b)` lies in the source set for `b, m ≥ 1` and `b * m ≤ X`.
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1a, hp1b⟩ := Finset.mem_product.mp hp1
    obtain ⟨hp1l, hp1u⟩ := Finset.mem_Icc.mp hp1a
    obtain ⟨hp2l, hp2u⟩ := Finset.mem_Icc.mp hp1b
    have hppos : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    dsimp only
    exact ⟨⟨by omega, hp2⟩, dvd_mul_right _ _, by omega⟩
  · -- Left inverse: `b * (n / b) = n` for `b ∣ n`.
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
    rcases a with ⟨n, b⟩
    obtain ⟨hbdvd, _⟩ := Nat.mem_divisors.mp ha2
    dsimp only
    rw [Nat.mul_div_cancel' hbdvd]
  · -- Right inverse: `(b * m) / b = m` for `b ≥ 1`.
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1a, _⟩ := Finset.mem_product.mp hp1
    obtain ⟨hp1l, _⟩ := Finset.mem_Icc.mp hp1a
    rcases p with ⟨b, m⟩
    dsimp only at hp1l ⊢
    rw [Nat.mul_div_right m (by omega : 0 < b)]
  · -- The integrands agree.
    intro a ha
    rfl

end Work.FIArea7
