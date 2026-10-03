import Mathlib

namespace Work.OROneRel

theorem int_level_sep (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (j k : ℕ) (hj : j < p) (hk : k < q) :
    (j : ℤ) * (q : ℤ) ≠ ((p * q : ℕ) : ℤ) - (k : ℤ) * (p : ℤ) := by
  intro h
  -- Move everything to ℕ: from the equality over ℤ we get `j*q = p*q - k*p`.
  have hle : k * p ≤ p * q := by
    rw [Nat.mul_comm k p]
    exact Nat.mul_le_mul_left p (le_of_lt hk)
  have hsub : ((p * q - k * p : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) - (k : ℤ) * (p : ℤ) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hZ : ((j * q : ℕ) : ℤ) = ((p * q - k * p : ℕ) : ℤ) := by
    rw [hsub]
    push_cast
    exact h
  have h2 : j * q = p * q - k * p := Nat.cast_injective hZ
  -- Rewrite the right-hand side as `p * (q - k)`.
  have h3 : j * q = p * (q - k) := by
    rw [h2, Nat.mul_comm k p, ← Nat.mul_sub_left_distrib]
  -- Since `p` is coprime to `q` and `p ∣ j*q`, we get `p ∣ j`, hence `j = 0`.
  have hdvd : p ∣ j := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hcop
    exact ⟨q - k, h3⟩
  have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hj
  -- Then `p * (q - k) = 0`, and since `p ≥ 1` we conclude `q ≤ k`, contradicting `k < q`.
  have hpq : p * (q - k) = 0 := by
    have h' := h3
    rw [hj0] at h'
    simpa using h'.symm
  have hqk : q - k = 0 := by
    rcases Nat.mul_eq_zero.mp hpq with hp0 | hqk
    · omega
    · exact hqk
  have hqk_le : q ≤ k := Nat.sub_eq_zero_iff_le.mp hqk
  omega

end Work.OROneRel
