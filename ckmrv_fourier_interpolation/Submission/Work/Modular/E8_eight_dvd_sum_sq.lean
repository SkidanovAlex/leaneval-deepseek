import Mathlib

namespace Work.Modular

open Finset

/-- Integer core of the parity of the `E₈` norm: if the coordinates `d i` are pairwise congruent modulo `2` (witnessed against `d 0`) and their sum is divisible by `4`, then the sum of their squares is divisible by `8`. -/
theorem E8_eight_dvd_sum_sq {d : Fin 8 → ℤ} (hpar : ∀ i, ∃ m : ℤ, d i - d 0 = 2 * m)
    (h4 : (4 : ℤ) ∣ ∑ i, d i) : (8 : ℤ) ∣ ∑ i, d i ^ 2 := by
  classical
  -- All coordinates share the parity of `d 0`: write `d i = d 0 + 2 * m i`.
  choose m hm using hpar
  have hd : ∀ i, d i = d 0 + 2 * m i := fun i => by have := hm i; linarith
  -- Sum of the coordinates.
  have hs : ∑ i, d i = 8 * d 0 + 2 * (∑ i, m i) := by
    rw [Finset.sum_congr rfl (fun i _ => hd i), Finset.sum_add_distrib, Finset.sum_const,
        ← Finset.mul_sum]
    simp
  -- Divisibility by `4` of the coordinate sum forces `∑ i, m i` to be even.
  have h4t : (4 : ℤ) ∣ 2 * (∑ i, m i) := by
    have h8 : (4 : ℤ) ∣ 8 * d 0 := ⟨2 * d 0, by ring⟩
    rw [hs] at h4
    exact (Int.dvd_add_right h8).mp h4
  have ht : (2 : ℤ) ∣ ∑ i, m i := by
    obtain ⟨k, hk⟩ := h4t
    exact ⟨k, by linarith⟩
  -- Sum of the squares.
  have hq : ∑ i, d i ^ 2 = 8 * d 0 ^ 2 + 4 * d 0 * (∑ i, m i) + 4 * ∑ i, m i ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hd i])]
    have hterm : ∀ i, (d 0 + 2 * m i) ^ 2 = d 0 ^ 2 + (4 * d 0 * m i + 4 * m i ^ 2) :=
      fun i => by ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
        ← Finset.mul_sum, ← Finset.mul_sum]
    simp
    ring
  -- `∑ i, m i ^ 2` is also even, since `m ^ 2 - m` is always even.
  have hsqeven : (2 : ℤ) ∣ ∑ i, m i ^ 2 := by
    have h_each : ∀ i, (2 : ℤ) ∣ m i ^ 2 - m i := fun i => by
      rw [show m i ^ 2 - m i = (m i - 1) * ((m i - 1) + 1) by ring]
      exact even_iff_two_dvd.mp (Int.even_mul_succ_self (m i - 1))
    have hsum : (2 : ℤ) ∣ ∑ i, (m i ^ 2 - m i) := Finset.dvd_sum (fun i _ => h_each i)
    rw [Finset.sum_sub_distrib] at hsum
    have h' : (2 : ℤ) ∣ (∑ i, m i ^ 2 - ∑ i, m i) + ∑ i, m i := dvd_add hsum ht
    rwa [sub_add_cancel] at h'
  rw [hq]
  have h1 : (8 : ℤ) ∣ 8 * d 0 ^ 2 := ⟨d 0 ^ 2, by ring⟩
  have h2 : (8 : ℤ) ∣ 4 * d 0 * (∑ i, m i) := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨d 0 * k, by rw [hk]; ring⟩
  have h3 : (8 : ℤ) ∣ 4 * ∑ i, m i ^ 2 := by
    obtain ⟨k, hk⟩ := hsqeven
    exact ⟨k, by rw [hk]; ring⟩
  exact dvd_add (dvd_add h1 h2) h3

end Work.Modular
