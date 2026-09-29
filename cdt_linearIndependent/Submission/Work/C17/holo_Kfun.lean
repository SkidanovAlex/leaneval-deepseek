/-
Auxiliary estimates for `Work.C17.logP_not_holomorphic_at_xs`:

* `alpha_mul_rho`: `(x + √(x²−1))·(x − √(x²−1)) = 1`;
* `xs_eq_div`: `xs a b = (a + √(a²−1))/(b + √(b²−1))`;
* `xs_pos_and_lt_one`: `0 < xs a b` and `xs a b · xs a b < 1` for `3 ≤ a < b`;
* `Kfun_bound_alt` (renamed to avoid a clash with `Submission.Work.C17.Kfun_bound`):
  the remainder coefficients `K n` grow at most like `C (n+1)⁴ xsⁿ`.
-/
import Mathlib
import Submission.Work.C17.logP_defs

namespace Work.C17

open scoped BigOperators

lemma alpha_mul_rho (x : ℝ) (hx : 1 ≤ x) :
    (x + Real.sqrt (x ^ 2 - 1)) * (x - Real.sqrt (x ^ 2 - 1)) = 1 := by
  have h : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  nlinarith

lemma alpha_pos (x : ℝ) (hx : 1 ≤ x) : 0 < x + Real.sqrt (x ^ 2 - 1) := by
  have h : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

lemma xs_eq_div (a b : ℚ) (hb : 1 ≤ (b : ℝ)) :
    xs a b = ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1))
      / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) := by
  have h := alpha_mul_rho (b : ℝ) hb
  have hne : (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) ≠ 0 :=
    ne_of_gt (alpha_pos (b : ℝ) hb)
  unfold xs
  rw [eq_div_iff hne]
  rw [mul_assoc,
    mul_comm ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)),
    h, mul_one]

lemma xs_pos_and_lt_one (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b) :
    0 < xs a b ∧ xs a b * xs a b < 1 := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
    have h : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    have h : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hxs := xs_eq_div a b hb1
  have hA0 : 0 < (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) := alpha_pos (a : ℝ) ha1
  have hB0 : 0 < (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) := alpha_pos (b : ℝ) hb1
  have hlt : (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)
      < (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    have h1 : (a : ℝ) ^ 2 - 1 < (b : ℝ) ^ 2 - 1 := by nlinarith
    have h2 : Real.sqrt ((a : ℝ) ^ 2 - 1) < Real.sqrt ((b : ℝ) ^ 2 - 1) :=
      Real.sqrt_lt_sqrt (by nlinarith) h1
    linarith
  have h0 : 0 < ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1))
      / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) := div_pos hA0 hB0
  have h1 : ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1))
      / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) < 1 := (div_lt_one hB0).mpr hlt
  rw [hxs]
  exact ⟨h0, by nlinarith [h0, h1]⟩

theorem Kfun_bound_alt (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (ra rb rab : ℤ) (C : ℝ)
    (hdahi : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
    (hdbhi : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n)
    (huahi : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n
        ≤ ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ,
      |Kfun a b ra rb rab n| ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
    have h : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    have h : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  set A : ℝ := (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) with hA
  set B : ℝ := (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) with hB
  have hA0 : 0 < A := by rw [hA]; exact alpha_pos (a : ℝ) ha1
  have hB0 : 0 < B := by rw [hB]; exact alpha_pos (b : ℝ) hb1
  have hA1 : 1 ≤ A := by rw [hA]; linarith [ha1, Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1)]
  have hxsAB : xs a b = A / B := by rw [hA, hB]; exact xs_eq_div a b hb1
  have hxs0 : 0 ≤ xs a b := by rw [hxsAB]; exact le_of_lt (div_pos hA0 hB0)
  have hub : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n ≤ A ^ n := by
    intro n; rw [hA]; exact huahi n
  have hua : ∀ n : ℕ, 0 ≤ Submission.CDT.beukersUR (a : ℝ) n := fun n =>
    le_of_lt (Submission.CDT.beukersUR_pos (a : ℝ) ha1 n)
  have hda : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
      ≤ (|C| + 1) * ((n : ℝ) + 1) ^ 2 / A ^ n := by
    intro n
    rw [hA]
    refine le_trans (hdahi n) ?_
    refine div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity))
      (pow_nonneg (le_of_lt (alpha_pos (a : ℝ) ha1)) n)
  have hdb : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n|
      ≤ (|C| + 1) * ((n : ℝ) + 1) ^ 2 / B ^ n := by
    intro n
    rw [hB]
    refine le_trans (hdbhi n) ?_
    refine div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity))
      (pow_nonneg (le_of_lt (alpha_pos (b : ℝ) hb1)) n)
  have hpiece1 : ∀ n : ℕ,
      |Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n|
      ≤ (|C| + 1) * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by
    intro n
    rw [abs_mul, abs_of_nonneg (hua n), hxsAB]
    calc Submission.CDT.beukersUR (a : ℝ) n * |Submission.CDT.beukersD (b : ℝ) n|
        ≤ A ^ n * ((|C| + 1) * ((n : ℝ) + 1) ^ 2 / B ^ n) :=
          mul_le_mul (hub n) (hdb n) (abs_nonneg _) (pow_nonneg (le_of_lt hA0) n)
      _ = (|C| + 1) * ((n : ℝ) + 1) ^ 2 * (A / B) ^ n := by
          rw [div_pow]; ring
      _ ≤ (|C| + 1) * ((n : ℝ) + 1) ^ 4 * (A / B) ^ n := by
          have h1 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
            have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
              have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
              linarith
            calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := (mul_one _).symm
              _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
                  mul_le_mul_of_nonneg_left (one_le_pow₀ h2) (by positivity)
              _ = ((n : ℝ) + 1) ^ 4 := by ring
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
  have hpiece2 : ∀ n : ℕ,
      |Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n|
      ≤ (|C| + 1) ^ 2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by
    intro n
    rw [abs_mul, hxsAB]
    have hAB_le : (1 : ℝ) / (A * B) ≤ A / B := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < A * B) hB0]
      have hA2 : (1 : ℝ) ≤ A * A := by nlinarith [hA1]
      have h4 : (A * A) * B = A * (A * B) := by ring
      rw [← h4]
      exact mul_le_mul_of_nonneg_right hA2 (le_of_lt hB0)
    have hnonneg : (0 : ℝ) ≤ 1 / (A * B) := by positivity
    calc |Submission.CDT.beukersD (a : ℝ) n| * |Submission.CDT.beukersD (b : ℝ) n|
        ≤ ((|C| + 1) * ((n : ℝ) + 1) ^ 2 / A ^ n)
            * ((|C| + 1) * ((n : ℝ) + 1) ^ 2 / B ^ n) :=
          mul_le_mul (hda n) (hdb n) (abs_nonneg _)
            (div_nonneg (mul_nonneg (by positivity) (by positivity))
              (pow_nonneg (le_of_lt hA0) n))
      _ = (|C| + 1) ^ 2 * ((n : ℝ) + 1) ^ 4 * (1 / (A * B)) ^ n := by
          rw [one_div, inv_pow, mul_pow, mul_inv]
          ring
      _ ≤ (|C| + 1) ^ 2 * ((n : ℝ) + 1) ^ 4 * (A / B) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hAB_le n) (by positivity)
  set E : ℝ := (rb : ℝ) + (rab : ℝ) * Submission.CDT.beukersEta (a : ℝ) with hE
  refine ⟨(|E| * (|C| + 1) + |(rab : ℝ)| * (|C| + 1) ^ 2) + 1, by positivity, fun n => ?_⟩
  rw [Kfun, ← hE]
  calc |E * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)
        + (rab : ℝ) * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
      ≤ |E * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)|
        + |(rab : ℝ) * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)| :=
          abs_add_le _ _
    _ = |E| * |Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n|
        + |(rab : ℝ)| * |Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n| := by
          simp only [abs_mul]
    _ ≤ |E| * ((|C| + 1) * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n)
        + |(rab : ℝ)| * ((|C| + 1) ^ 2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpiece1 n) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hpiece2 n) (abs_nonneg _))
    _ = (|E| * (|C| + 1) + |(rab : ℝ)| * (|C| + 1) ^ 2) * (((n : ℝ) + 1) ^ 4 * (xs a b) ^ n) := by
          ring
    _ ≤ ((|E| * (|C| + 1) + |(rab : ℝ)| * (|C| + 1) ^ 2) + 1)
          * (((n : ℝ) + 1) ^ 4 * (xs a b) ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg (by positivity) (pow_nonneg hxs0 n))
    _ = ((|E| * (|C| + 1) + |(rab : ℝ)| * (|C| + 1) ^ 2) + 1)
          * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by ring

end Work.C17
