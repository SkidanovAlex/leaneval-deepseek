import Mathlib
import Submission.Work.HP.DyadicDefs

namespace Work.HP.dyadic

/-- Arithmetic comparison used in the dyadic-sum bookkeeping: the factor
`2 ^ ((N-2) * ⌈L⌉₊) * (⌈L⌉₊ + 1)^2` is bounded by a constant (depending only on
`N`) times `2 ^ ((N-2) * L) * (1 + L)^2`.  This is the elementary step that lets
one replace the ceiling `⌈L⌉₊` of a real scale by `L` itself, at the cost of a
constant factor `4 * 2 ^ (N-2)`. -/
theorem L_arith (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 ≤ L →
      (2:ℝ) ^ ((N-2) * ⌈L⌉₊) * (⌈L⌉₊ + 1)^2 ≤ C * 2 ^ ((N-2)*L) * (1+L)^2 := by
  refine ⟨4 * (2:ℝ) ^ ((N:ℝ)-2), by positivity, ?_⟩
  intro L hL
  -- `⌈L⌉₊ ≤ L + 1`.
  have hk : ((⌈L⌉₊ : ℕ) : ℝ) ≤ L + 1 := le_of_lt (Nat.ceil_lt_add_one hL)
  -- `0 ≤ N - 2`.
  have ha0 : (0:ℝ) ≤ (N:ℝ) - 2 := by
    have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  -- Exponent comparison: `((N-2) * ⌈L⌉₊) ≤ (N-2) * L + (N-2)`.
  have hexp : (((N-2) * ⌈L⌉₊ : ℕ) : ℝ) ≤ ((N:ℝ)-2)*L + ((N:ℝ)-2) := by
    have hcast : (((N-2) * ⌈L⌉₊ : ℕ) : ℝ) = ((N:ℝ)-2) * ((⌈L⌉₊:ℕ):ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hN]
      norm_num
    rw [hcast]
    have h1 : ((N:ℝ)-2) * ((⌈L⌉₊:ℕ):ℝ) ≤ ((N:ℝ)-2) * (L+1) :=
      mul_le_mul_of_nonneg_left hk ha0
    linarith
  -- Bounding the power of two.
  have hA : (2:ℝ) ^ ((N-2) * ⌈L⌉₊) ≤ (2:ℝ) ^ ((N:ℝ)-2) * 2 ^ (((N:ℝ)-2)*L) := by
    calc (2:ℝ) ^ ((N-2) * ⌈L⌉₊)
        = (2:ℝ) ^ ((((N-2) * ⌈L⌉₊ : ℕ)) : ℝ) := (Real.rpow_natCast 2 _).symm
      _ ≤ (2:ℝ) ^ (((N:ℝ)-2)*L + ((N:ℝ)-2)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (2:ℝ) ^ (((N:ℝ)-2)*L) * (2:ℝ) ^ ((N:ℝ)-2) := by
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      _ = (2:ℝ) ^ ((N:ℝ)-2) * 2 ^ (((N:ℝ)-2)*L) := by rw [mul_comm]
  -- Bounding the quadratic factor.
  have hB : ((⌈L⌉₊ : ℝ) + 1)^2 ≤ 4 * (1+L)^2 := by
    have hx : (⌈L⌉₊ : ℝ) + 1 ≤ 2*(1+L) := by linarith
    have h0 : (0:ℝ) ≤ (⌈L⌉₊ : ℝ) + 1 := by positivity
    have h := pow_le_pow_left₀ h0 hx 2
    nlinarith [h]
  calc (2:ℝ) ^ ((N-2) * ⌈L⌉₊) * (⌈L⌉₊ + 1)^2
      ≤ ((2:ℝ) ^ ((N:ℝ)-2) * 2 ^ (((N:ℝ)-2)*L)) * (4 * (1+L)^2) := by
          apply mul_le_mul hA hB <;> positivity
    _ = (4 * (2:ℝ) ^ ((N:ℝ)-2)) * 2 ^ (((N:ℝ)-2)*L) * (1+L)^2 := by ring

end Work.HP.dyadic
