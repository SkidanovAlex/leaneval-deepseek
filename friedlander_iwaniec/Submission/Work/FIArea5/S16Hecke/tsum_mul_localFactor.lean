import Mathlib

namespace Work.FIArea5.S16Hecke

theorem tsum_mul_localFactor {a : ℕ → ℂ} {A C z : ℂ}
    (hsum : Summable (fun ν : ℕ => a ν * z ^ ν))
    (h0 : a 0 = 1) (hA : A = a 1)
    (hrec : ∀ ν : ℕ, a (ν + 2) = A * a (ν + 1) - C * a ν) :
    (∑' ν : ℕ, a ν * z ^ ν) * (1 - A * z + C * z ^ 2) = 1 := by
  set S : ℂ := ∑' ν : ℕ, a ν * z ^ ν with hS
  have hf0 : a 0 * z ^ 0 = 1 := by rw [h0]; ring
  have hf1 : a 1 * z ^ 1 = A * z := by rw [← hA]; ring
  have hsum1 : Summable (fun n : ℕ => a (n+1) * z ^ (n+1)) :=
    (summable_nat_add_iff 1).2 hsum
  -- Termwise rewrite of the recurrence in generating-function form.
  have key : ∀ n : ℕ, a (n+2) * z ^ (n+2) =
      (A*z) * (a (n+1) * z ^ (n+1)) - (C*z^2) * (a n * z ^ n) := by
    intro n
    rw [hrec n]
    ring_nf
  -- Tail identity for the shift by 2.
  have e1 : (∑' n : ℕ, a (n+2) * z ^ (n+2)) = S - (a 0 * z^0) - (a 1 * z^1) := by
    have h := Summable.sum_add_tsum_nat_add 2 hsum
    rw [← hS] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    linear_combination h
  -- Tail identity for the shift by 1.
  have e3 : (∑' n : ℕ, a (n+1) * z ^ (n+1)) = S - (a 0 * z^0) := by
    have h := Summable.sum_add_tsum_nat_add 1 hsum
    rw [← hS] at h
    simp only [Finset.sum_range_one] at h
    linear_combination h
  -- Split the shifted sum using the recurrence and reindex by constants.
  have hsplit : (∑' n : ℕ, a (n+2) * z ^ (n+2)) =
      (A*z) * (∑' n : ℕ, a (n+1) * z ^ (n+1)) - (C*z^2) * S := by
    rw [tsum_congr key]
    rw [Summable.tsum_sub (hsum1.mul_left (A*z)) (hsum.mul_left (C*z^2))]
    rw [tsum_mul_left, tsum_mul_left]
  have e2 : (∑' n : ℕ, a (n+2) * z ^ (n+2)) = (A*z) * (S - (a 0 * z^0)) - (C*z^2) * S := by
    rw [hsplit, e3]
  have eq : S - (a 0 * z^0) - (a 1 * z^1) = (A*z) * (S - (a 0 * z^0)) - (C*z^2) * S :=
    e1.symm.trans e2
  have eq' : S - 1 - A*z = (A*z) * (S - 1) - (C*z^2) * S := by
    rw [hf0, hf1] at eq
    exact eq
  linear_combination eq'

end Work.FIArea5.S16Hecke
