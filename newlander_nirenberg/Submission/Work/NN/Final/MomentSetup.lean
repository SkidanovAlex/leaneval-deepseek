import Mathlib

/-! Setup for the Seeley moment data construction.

We build the entire function `Bfun u = ∏_{p≥1} (1 - u/3^p)` through its Taylor
coefficients `mcoef`, which satisfy `mcoef 0 = 1` and the recursion
`mcoef (n+1) = -mcoef n / (3^(n+1) - 1)` coming from the functional equation
`Bfun (3u) = (1-u) * Bfun u`. -/

namespace Work.NN.Final

/-- Coefficients of `∏_{p≥1} (1 - z/3^p)`. -/
noncomputable def mcoef : ℕ → ℝ
  | 0 => 1
  | (n + 1) => -(mcoef n) / ((3 : ℝ) ^ (n + 1) - 1)

/-- `Bfun u = ∑' n, mcoef n * u^n`. -/
noncomputable def Bfun (u : ℝ) : ℝ := ∑' n, mcoef n * u ^ n

/-- The normalising constant `mkappa = Bfun 1 = ∏_{p≥1} (1 - 3^{-p})`. -/
noncomputable def mkappa : ℝ := ∑' n, mcoef n

@[simp] lemma mcoef_zero : mcoef 0 = 1 := rfl

lemma mcoef_succ (n : ℕ) : mcoef (n + 1) = -(mcoef n) / ((3 : ℝ) ^ (n + 1) - 1) := rfl

lemma three_pow_ge_real (n : ℕ) : (2:ℝ) * (n + 1) ≤ (3:ℝ) ^ (n + 1) - 1 := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; push_cast; nlinarith [ih, pow_pos (by norm_num : (0:ℝ) < 3) (k+1)]

lemma mcoef_bound_aux : ∀ n, |mcoef n| * (n.factorial:ℝ) * (2:ℝ)^n ≤ 1 := by
  intro n
  induction n with
  | zero => norm_num [mcoef]
  | succ k ih =>
    have hD : (0:ℝ) < (3:ℝ)^(k+1) - 1 := by linarith [three_pow_ge_real k]
    have hkey : (2:ℝ)*(k+1) ≤ (3:ℝ)^(k+1) - 1 := three_pow_ge_real k
    have hfac : ((k+1).factorial : ℝ) = ((k:ℝ)+1) * (k.factorial:ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [mcoef_succ, abs_div, abs_neg, abs_of_pos hD]
    have hsplit : |mcoef k| / ((3:ℝ)^(k+1)-1) * ((k+1).factorial:ℝ) * (2:ℝ)^(k+1)
        = (|mcoef k| * (k.factorial:ℝ) * (2:ℝ)^k) * ((2*(k+1))/((3:ℝ)^(k+1)-1)) := by
      rw [hfac, pow_succ]; field_simp; ring
    rw [hsplit]
    calc (|mcoef k| * (k.factorial:ℝ) * (2:ℝ)^k) * ((2*(k+1))/((3:ℝ)^(k+1)-1))
        ≤ 1 * ((2*(k+1))/((3:ℝ)^(k+1)-1)) := by
          apply mul_le_mul_of_nonneg_right ih; positivity
      _ ≤ 1 := by rw [one_mul, div_le_one hD]; exact hkey

lemma mcoef_bound (n : ℕ) : |mcoef n| ≤ 1 / ((n.factorial:ℝ) * (2:ℝ)^n) := by
  rw [le_div_iff₀ (by positivity)]
  simpa only [mul_assoc] using mcoef_bound_aux n

lemma mcoef_summable (u : ℝ) : Summable (fun n => mcoef n * u^n) := by
  apply Summable.of_norm_bounded (g := fun n => (|u|/2)^n / (n.factorial:ℝ))
  · exact Real.summable_pow_div_factorial (|u|/2)
  · intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |mcoef n| ≤ 1 / ((n.factorial:ℝ) * (2:ℝ)^n) := mcoef_bound n
    calc |mcoef n| * |u|^n ≤ (1 / ((n.factorial:ℝ) * (2:ℝ)^n)) * |u|^n := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (|u|/2)^n / (n.factorial:ℝ) := by rw [div_pow]; ring

lemma mkappa_summable : Summable mcoef := by simpa using mcoef_summable 1

lemma Bfun_zero : Bfun 0 = 1 := by
  rw [Bfun, tsum_eq_single 0]
  · norm_num [mcoef]
  · intro n hn
    rw [zero_pow hn, mul_zero]

lemma Bfun_eq (u : ℝ) : Bfun u = ∑' n, mcoef n * u ^ n := rfl

end Work.NN.Final
