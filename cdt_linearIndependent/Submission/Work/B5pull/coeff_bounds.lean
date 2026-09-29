import Mathlib
import Submission.Work.Pure.interfaces

/-!
# `coeff_bounds`: exponential bounds for the coefficients of `B₂` and `B₅`

The two pure power series

* `B₂ = Σ_{n≥2} 2 (n-2)! n!/(2n)! · yⁿ`,
* `B₅ = Σ_{n≥1} (n-1)!²/((2n-1)!(2n-1)) · yⁿ`

have factorially small coefficients.  In this file we prove the crude but sufficient
exponential bounds

`‖[yⁿ]B₅‖ ≤ 4 · (1/4)ⁿ`,   `‖[yⁿ]B₂‖ ≤ 10 · (1/4)ⁿ`   (`n : ℕ`).

The proof is elementary:  writing `aₙ` for the `n`-th coefficient (in `ℝ`), one checks the
one-step ratios

`a_{n+1} / a_n = n(2n-1)/(2(2n+1)²) ≤ 1/4`  (for `B₅`),
`a_{n+1} / a_n = (n-1)/(2(2n+1))     ≤ 1/4`  (for `B₂`),

so the coefficients decay geometrically with ratio at most `1/4`; the two constants `4` and
`10` absorb the first one or two terms.
-/

namespace Work.B5pull

open PowerSeries

/-! ## The norm of a rational, cast to `ℂ` -/

lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by
  rw [← Complex.ofReal_ratCast]; simp

/-! ## Coefficient formulas

We extract the (rational) coefficients of `B₅` and `B₂` from the definitions in
`Submission.CDTPlan.Interfaces` and rewrite them as real numbers. -/

/-- The `n`-th coefficient of `B₅`, as a real number. -/
noncomputable def k5 (n : ℕ) : ℝ := ((n - 1).factorial : ℝ) ^ 2 / ((2 * n - 1).factorial : ℝ)

/-- `k5` divided by the extra factor `2n-1`. -/
noncomputable def c5 (n : ℕ) : ℝ := k5 n / (2 * (n : ℝ) - 1)

/-- The `n`-th coefficient of `B₂`, as a real number. -/
noncomputable def k2 (n : ℕ) : ℝ :=
  2 * ((n - 2).factorial : ℝ) * (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

lemma coeff_B5_real (n : ℕ) (hn : 1 ≤ n) :
    ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℝ) = c5 n := by
  have h : PowerSeries.coeff n Submission.CDTPlan.B5
      = ((n - 1).factorial : ℚ) ^ 2 / (((2 * n - 1).factorial : ℚ) * (2 * (n : ℚ) - 1)) := by
    simp only [Submission.CDTPlan.B5, PowerSeries.coeff_mk]
    rw [if_neg (by omega : ¬ n = 0)]
  rw [h]
  simp only [c5, k5]
  push_cast
  field_simp

lemma coeff_B2_real (n : ℕ) (hn : 2 ≤ n) :
    ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℝ) = k2 n := by
  have h : PowerSeries.coeff n Submission.CDTPlan.B2
      = 2 * (((n - 2).factorial : ℚ) * (n.factorial : ℚ)) / ((2 * n).factorial : ℚ) := by
    simp only [Submission.CDTPlan.B2, PowerSeries.coeff_mk]
    rw [if_neg (by omega : ¬ n < 2)]
  rw [h]
  simp only [k2]
  push_cast
  ring

/-! ## The recursion and the geometric decay for `B₅` -/

lemma k5_succ (n : ℕ) (hn : 1 ≤ n) :
    k5 (n + 1) = ((n : ℝ) ^ 2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1))) * k5 n := by
  unfold k5
  have e1 : n + 1 - 1 = n := by omega
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [e1, e2]
  have f1 : ((n.factorial : ℕ) : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h
    rw [h]; push_cast; ring
  have f2 : (((2 * n + 1).factorial : ℕ) : ℝ) =
      (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) * (((2 * n - 1).factorial : ℕ) : ℝ) := by
    have h1 := Nat.factorial_succ (2 * n)
    have h2 := Nat.factorial_succ (2 * n - 1)
    rw [show 2 * n - 1 + 1 = 2 * n from by omega] at h2
    rw [h2] at h1
    rw [h1]; push_cast; ring
  rw [f1, f2]
  have hA : (((2 * n - 1).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n - 1)
  have hB : (((n - 1).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have hC : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hD : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma k5_nonneg (n : ℕ) : 0 ≤ k5 n := by unfold k5; positivity

lemma c5_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ c5 n := by
  have hk : 0 ≤ k5 n := k5_nonneg n
  have hd : 0 < 2 * (n : ℝ) - 1 := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  simp only [c5]
  exact div_nonneg hk (le_of_lt hd)

/-- One-step decay for the coefficients of `B₅`. -/
lemma c5_succ_le (n : ℕ) (hn : 1 ≤ n) : c5 (n + 1) ≤ (1 / 4) * c5 n := by
  have hk := k5_succ n hn
  have hknn : 0 ≤ k5 n := k5_nonneg n
  have hcoef : (n : ℝ) ^ 2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2)
      ≤ 1 / (4 * (2 * (n : ℝ) - 1)) := by
    have hpoly : (n : ℝ) ^ 2 * (4 * (2 * (n : ℝ) - 1))
        ≤ 2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [sq_nonneg ((n : ℝ))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2)]
    rw [show (1 / (4 * (2 * (n : ℝ) - 1))) * (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2)
          = (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2) / (4 * (2 * (n : ℝ) - 1)) by ring]
    rw [le_div_iff₀ (by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith)]
    exact hpoly
  have hden : (2 * ((n + 1 : ℕ) : ℝ) - 1) = 2 * (n : ℝ) + 1 := by push_cast; ring
  have hstep : c5 (n + 1) = ((n : ℝ) ^ 2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2)) * k5 n := by
    simp only [c5, hk, hden]
    field_simp
  rw [hstep]
  calc ((n : ℝ) ^ 2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ 2)) * k5 n
      ≤ (1 / (4 * (2 * (n : ℝ) - 1))) * k5 n := by nlinarith [hknn]
    _ = (1 / 4) * c5 n := by
        simp only [c5]
        field_simp

/-- Geometric bound for the coefficients of `B₅`. -/
lemma c5_le (n : ℕ) (hn : 1 ≤ n) : c5 n ≤ 4 * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        norm_num [c5, k5]
      · calc c5 (k + 1) ≤ (1 / 4) * c5 k := c5_succ_le k hk
          _ ≤ (1 / 4) * (4 * (1 / 4 : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left (ih hk) (by norm_num)
          _ = 4 * (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-! ## The recursion and the geometric decay for `B₂` -/

lemma k2_succ (n : ℕ) (hn : 2 ≤ n) :
    k2 (n + 1) = ((n : ℝ) - 1) / (2 * (2 * (n : ℝ) + 1)) * k2 n := by
  unfold k2
  have e1 : n + 1 - 2 = n - 1 := by omega
  have e2 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [e1, e2]
  have f1 : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
    have h := Nat.factorial_succ n
    rw [h]; push_cast; ring
  have f2 : (((n - 1).factorial : ℕ) : ℝ) = ((n : ℝ) - 1) * (((n - 2).factorial : ℕ) : ℝ) := by
    have h := Nat.factorial_succ (n - 2)
    rw [show n - 2 + 1 = n - 1 from by omega] at h
    rw [h, Nat.cast_mul, Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
  have f3 : (((2 * n + 2).factorial : ℕ) : ℝ) =
      (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (((2 * n).factorial : ℕ) : ℝ) := by
    have h1 := Nat.factorial_succ (2 * n + 1)
    have h2 := Nat.factorial_succ (2 * n)
    rw [h2] at h1
    rw [h1]; push_cast; ring
  rw [f1, f2, f3]
  have ha : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hb : (((n - 2).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2)
  have hc : (((n).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hd : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have he : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  field_simp

lemma k2_nonneg (n : ℕ) : 0 ≤ k2 n := by unfold k2; positivity

/-- One-step decay for the coefficients of `B₂`. -/
lemma k2_succ_le (n : ℕ) (hn : 2 ≤ n) : k2 (n + 1) ≤ (1 / 4) * k2 n := by
  rw [k2_succ n hn]
  have hknn : 0 ≤ k2 n := k2_nonneg n
  have hcoef : ((n : ℝ) - 1) / (2 * (2 * (n : ℝ) + 1)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * (n : ℝ) + 1))]
    linarith
  exact mul_le_mul_of_nonneg_right hcoef hknn

lemma k2_le (n : ℕ) (hn : 2 ≤ n) : k2 n ≤ 10 * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
      rcases lt_or_ge k 2 with hk | hk
      · interval_cases k
        · omega
        · norm_num [k2]
      · calc k2 (k + 1) ≤ (1 / 4) * k2 k := k2_succ_le k hk
          _ ≤ (1 / 4) * (10 * (1 / 4 : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left (ih hk) (by norm_num)
          _ = 10 * (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-! ## The target -/

theorem coeff_bounds :
    (∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)‖ ≤ 4 * (1 / 4 : ℝ) ^ n) ∧
    (∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ 10 * (1 / 4 : ℝ) ^ n) := by
  constructor
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show PowerSeries.coeff 0 Submission.CDTPlan.B5 = 0 from by
        simp [Submission.CDTPlan.B5]]
      simp
    · rw [norm_ratCast, coeff_B5_real n hn, abs_of_nonneg (c5_nonneg n hn)]
      exact c5_le n hn
  · intro n
    rcases lt_or_ge n 2 with hn | hn
    · rw [show PowerSeries.coeff n Submission.CDTPlan.B2 = 0 from by
        simp only [Submission.CDTPlan.B2, PowerSeries.coeff_mk]
        rw [if_pos hn]]
      simp
    · rw [norm_ratCast, coeff_B2_real n hn, abs_of_nonneg (k2_nonneg n)]
      exact k2_le n hn

end Work.B5pull
