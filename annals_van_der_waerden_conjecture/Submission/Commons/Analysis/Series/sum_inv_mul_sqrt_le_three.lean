import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt

namespace Commons.Analysis.Series

open Real

/-- Key termwise estimate: for `k ≥ 1`,
`1/((k+1)√(k+1)) ≤ 2 (1/√k - 1/√(k+1))`.
Summing this telescopes and bounds the partial sum by `3`. -/
lemma one_div_succ_mul_sqrt_le (k : ℕ) (hk : 1 ≤ k) :
    (1:ℝ) / (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))
      ≤ 2 * (1 / Real.sqrt (k:ℝ) - 1 / Real.sqrt ((k:ℝ)+1)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  set A := Real.sqrt (k:ℝ) with hAdef
  set B := Real.sqrt ((k:ℝ)+1) with hBdef
  have hA : 0 < A := by rw [hAdef]; exact Real.sqrt_pos_of_pos hk0
  have hB : 0 < B := by rw [hBdef]; exact Real.sqrt_pos_of_pos hk1
  have hA2 : A^2 = (k:ℝ) := by rw [hAdef]; exact Real.sq_sqrt (le_of_lt hk0)
  have hB2 : B^2 = (k:ℝ)+1 := by rw [hBdef]; exact Real.sq_sqrt (le_of_lt hk1)
  have hAB : A * B ≤ (k:ℝ) + 2 := by
    rw [hAdef, hBdef]
    have hkk0 : (0:ℝ) ≤ (k:ℝ) := le_of_lt hk0
    have h1 : Real.sqrt (k:ℝ) * Real.sqrt ((k:ℝ)+1)
        = Real.sqrt ((k:ℝ) * ((k:ℝ)+1)) := by
      rw [Real.sqrt_mul hkk0]
    rw [h1]
    calc Real.sqrt ((k:ℝ) * ((k:ℝ)+1)) ≤ Real.sqrt (((k:ℝ)+2) * ((k:ℝ)+2)) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = (k:ℝ) + 2 := by rw [Real.sqrt_mul_self (by positivity)]
  have hsq : (B - A) * (A + B) = 1 := by nlinarith [hA2, hB2]
  have hkey : A * (A + B) ≤ 2 * ((k:ℝ)+1) := by nlinarith [hAB, hA2]
  have hcore : A ≤ 2 * ((k:ℝ)+1) * (B - A) := by
    have hpos : 0 < A + B := by linarith
    nlinarith [hsq, hkey, hpos, sq_nonneg (A+B)]
  have hrew : (2:ℝ) * (1/A - 1/B) = 2*(B-A)/(A*B) := by
    field_simp
  rw [hrew]
  rw [div_le_div_iff₀ (mul_pos hk1 hB) (mul_pos hA hB)]
  nlinarith [hcore, hB]

theorem sum_inv_mul_sqrt_le_three (n : ℕ) :
    (∑ k ∈ Finset.range n, (1:ℝ) / ((k + 1 : ℝ) * Real.sqrt (k + 1))) ≤ 3 := by
  let f : ℕ → ℝ := fun k => 1 / (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))
  let G : ℕ → ℝ := fun k => 1 / Real.sqrt ((k:ℝ))
  change (∑ k ∈ Finset.range n, f k) ≤ 3
  have hf : ∀ k, 1 ≤ k → f k ≤ 2 * (G k - G (k+1)) := by
    intro k hk
    simpa [f, G] using one_div_succ_mul_sqrt_le k hk
  have key : ∀ m ≥ 1, (∑ k ∈ Finset.range m, f k) ≤ 3 - 2*G m := by
    apply Nat.le_induction
    · simp only [Finset.sum_range_one, f, G]
      norm_num [Real.sqrt_one]
    · intro m hm ih
      rw [Finset.sum_range_succ]
      calc (∑ k ∈ Finset.range m, f k) + f m
          ≤ (3 - 2*G m) + 2*(G m - G (m+1)) := add_le_add ih (hf m hm)
        _ = 3 - 2*G (m+1) := by ring
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hG : 0 ≤ G n := by
      simp only [G]; positivity
    have h := key n hn
    linarith

end Commons.Analysis.Series