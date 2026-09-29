import Mathlib
import Submission.Work.Resample.buQWdefs

namespace Work.Resample

/-!
# `Work.Resample.buHalveIn`

The size invariant `buIn` of the work vectors of the one-dimensional `B̃` word is preserved (up to
the factor `2^{-1}` and the rounding slack `2`) by the fixed-point halving `buHalve`.

The content is elementary: truncated halving of an integer `a` satisfies
`4 * ((a.tdiv 2).natAbs)^2 ≤ a.natAbs^2`, so halving a pair on a disc of radius `2^p` lands on a
disc of radius `2^{p-1}`; the additive `2` only has to absorb the rounding error.
-/

/-- Truncated halving shrinks the square by a factor `4`: `4 * ((a.tdiv 2).natAbs)^2 ≤ a.natAbs^2`. -/
theorem tdiv_two_natAbs_sq_mul_four_le (a : ℤ) :
    4 * ((a.tdiv 2).natAbs) ^ 2 ≤ a.natAbs ^ 2 := by
  rw [Int.natAbs_tdiv, show ((2 : ℤ).natAbs) = 2 from rfl]
  have h1 : a.natAbs / 2 * 2 ≤ a.natAbs := Nat.div_mul_le_self a.natAbs 2
  have h2 : (a.natAbs / 2 * 2) ^ 2 ≤ a.natAbs ^ 2 := Nat.pow_le_pow_left h1 2
  calc 4 * (a.natAbs / 2) ^ 2 = (a.natAbs / 2 * 2) ^ 2 := by ring
    _ ≤ a.natAbs ^ 2 := h2

/-- The `ℕ`-arithmetic core of `buHalveIn`: if `(M, N)` lies on the disc of radius `2^p` then its
halved coordinates lie on the disc of radius `2^(p-1) + 2`. -/
theorem div_two_sq_sum {p M N : ℕ} (h : M ^ 2 + N ^ 2 ≤ (2 ^ p) ^ 2) :
    (M / 2) ^ 2 + (N / 2) ^ 2 ≤ (2 ^ (p - 1) + 2) ^ 2 := by
  have hfour_le : ∀ m : ℕ, 4 * (m / 2) ^ 2 ≤ m ^ 2 := by
    intro m
    have h1 : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
    have h2 : (m / 2 * 2) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left h1 2
    calc 4 * (m / 2) ^ 2 = (m / 2 * 2) ^ 2 := by ring
      _ ≤ m ^ 2 := h2
  have hfour : 4 * ((M / 2) ^ 2 + (N / 2) ^ 2) ≤ (2 ^ p) ^ 2 := by
    have hdist : 4 * ((M / 2) ^ 2 + (N / 2) ^ 2)
        = 4 * (M / 2) ^ 2 + 4 * (N / 2) ^ 2 := by ring
    rw [hdist]
    have hM := hfour_le M
    have hN := hfour_le N
    omega
  rcases p with _ | q
  · have h4 : 4 * ((M / 2) ^ 2 + (N / 2) ^ 2) ≤ 1 := by simpa using hfour
    have h9 : (2 ^ (0 - 1) + 2) ^ 2 = 9 := by norm_num
    rw [h9]
    omega
  · have hpow : (2 ^ (q + 1)) ^ 2 = 4 * (2 ^ q) ^ 2 := by
      rw [pow_succ]; ring
    have h4 : 4 * ((M / 2) ^ 2 + (N / 2) ^ 2) ≤ 4 * (2 ^ q) ^ 2 := by
      rw [← hpow]; exact hfour
    have hX : (M / 2) ^ 2 + (N / 2) ^ 2 ≤ (2 ^ q) ^ 2 :=
      Nat.le_of_mul_le_mul_left h4 (by norm_num)
    have hfin : (2 ^ q) ^ 2 ≤ (2 ^ q + 2) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_add_right (2 ^ q) 2) 2
    exact le_trans hX (by simpa using hfin)

theorem buHalveIn (p : ℕ) (z : ℤ × ℤ) (h : Work.Resample.buIn (2 ^ p) z) :
    Work.Resample.buIn (2 ^ (p - 1) + 2) (Work.Resample.buHalve z) := by
  rcases z with ⟨a, b⟩
  have hh : a ^ 2 + b ^ 2 ≤ ((2 ^ p : ℕ) : ℤ) ^ 2 := h
  show (Int.tdiv a 2) ^ 2 + (Int.tdiv b 2) ^ 2 ≤ ((2 ^ (p - 1) + 2 : ℕ) : ℤ) ^ 2
  have hM : a.natAbs ^ 2 + b.natAbs ^ 2 ≤ (2 ^ p) ^ 2 := by
    have h' := hh
    rw [← Int.natAbs_sq a, ← Int.natAbs_sq b] at h'
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow] at h'
    exact_mod_cast h'
  have hnat : (a.natAbs / 2) ^ 2 + (b.natAbs / 2) ^ 2 ≤ (2 ^ (p - 1) + 2) ^ 2 :=
    div_two_sq_sum hM
  rw [← Int.natAbs_sq (a.tdiv 2), ← Int.natAbs_sq (b.tdiv 2), Int.natAbs_tdiv a 2,
    Int.natAbs_tdiv b 2, show ((2 : ℤ).natAbs) = 2 from rfl]
  push_cast
  exact_mod_cast hnat

end Work.Resample
