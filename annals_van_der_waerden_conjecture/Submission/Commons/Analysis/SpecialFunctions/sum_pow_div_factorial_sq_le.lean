import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds

namespace Commons.Analysis.SpecialFunctions

/-- Pairing identity: a sum over `range (2*N)` splits into consecutive pairs. -/
private lemma sum_range_two_mul_pair (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N), f k) =
      ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem sum_pow_div_factorial_sq_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ j ∈ Finset.range N, x ^ j / (((j.factorial : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (2 * Real.sqrt x) := by
  set y := 2 * Real.sqrt x with hy
  have hy_nonneg : 0 ≤ y := by rw [hy]; positivity
  have hy_sq : y ^ 2 = 4 * x := by
    rw [hy, mul_pow, Real.sq_sqrt hx]; norm_num
  have hy_pow : ∀ j : ℕ, y ^ (2 * j) = (4 : ℝ) ^ j * x ^ j := by
    intro j
    rw [pow_mul, hy_sq, mul_pow]
  have hterm : ∀ j : ℕ,
      x ^ j / (((j.factorial : ℕ) : ℝ) ^ 2) ≤
        y ^ (2 * j) / (((2 * j).factorial : ℕ) : ℝ) := by
    intro j
    have hchoose : (((2 * j).choose j : ℕ) : ℝ) ≤ (4 : ℝ) ^ j := by
      have h := Nat.choose_le_two_pow (2 * j) j
      have hpow : (2 : ℕ) ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
      rw [hpow] at h
      have h' : (((2 * j).choose j : ℕ) : ℝ) ≤ (((4 : ℕ) ^ j : ℕ) : ℝ) := by
        exact_mod_cast h
      simpa using h'
    have hfact : (((2 * j).factorial : ℕ) : ℝ) =
        (((2 * j).choose j : ℕ) : ℝ) * (((j.factorial : ℕ) : ℝ)) ^ 2 := by
      have hle : j ≤ 2 * j := by omega
      have h := Nat.choose_mul_factorial_mul_factorial hle
      have hsub : 2 * j - j = j := by omega
      rw [hsub] at h
      have hcast : ((((2 * j).choose j) * j.factorial * j.factorial : ℕ) : ℝ) =
          (((2 * j).factorial : ℕ) : ℝ) := by exact_mod_cast h
      rw [← hcast]
      push_cast
      ring
    have hreal : (((2 * j).factorial : ℕ) : ℝ) ≤
        (4 : ℝ) ^ j * (((j.factorial : ℕ) : ℝ)) ^ 2 := by
      rw [hfact]
      exact mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
    rw [hy_pow j]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc x ^ j * (((2 * j).factorial : ℕ) : ℝ)
        ≤ x ^ j * ((4 : ℝ) ^ j * (((j.factorial : ℕ) : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hreal (pow_nonneg hx j)
      _ = ((4 : ℝ) ^ j * x ^ j) * (((j.factorial : ℕ) : ℝ)) ^ 2 := by ring
  calc ∑ j ∈ Finset.range N, x ^ j / (((j.factorial : ℕ) : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.range N, y ^ (2 * j) / (((2 * j).factorial : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ ∑ j ∈ Finset.range N,
          (y ^ (2 * j) / (((2 * j).factorial : ℕ) : ℝ) +
           y ^ (2 * j + 1) / (((2 * j + 1).factorial : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun j _ =>
          le_add_of_nonneg_right
            (div_nonneg (pow_nonneg hy_nonneg _) (by positivity)))
    _ = ∑ k ∈ Finset.range (2 * N), y ^ k / (((k.factorial : ℕ) : ℝ)) :=
        (sum_range_two_mul_pair (fun k => y ^ k / (((k.factorial : ℕ) : ℝ))) N).symm
    _ ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy_nonneg (2 * N)
    _ = Real.exp (2 * Real.sqrt x) := by rw [hy]

end Commons.Analysis.SpecialFunctions