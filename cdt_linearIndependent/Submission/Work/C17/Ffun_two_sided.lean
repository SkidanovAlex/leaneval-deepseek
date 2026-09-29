import Mathlib
import Submission.Work.C17.logP_defs

/-!
# `Work.C17.Ffun_two_sided`

Two-sided bounds for the coefficients `Ffun a b n = dₙ(a)·uₙ(b)` of the overconvergent
part `(H(a) − η_a A(a)) ⋆ A(b)` of the unlikely series, of growth `xs a b = α_a·β_b`
with `α_a = a + √(a²−1)`, `β_b = b − √(b²−1) = 1/α_b`.

The content is: from the given two-sided bounds for `dₙ(a)` (decay `α_a^{-n}`, with a
polynomial factor `(n+1)²` and a lower bound with `(n+1)^{-4}`) and for `uₙ(b)`
(growth `α_b^n` up to `(n+1)`), deduce

`|Ffun a b n| ≤ C·(n+1)³/xs a b ^n`   and   `c/((n+1)⁵ · xs a b ^n) ≤ |Ffun a b n|`,

using `α_b·β_b = 1`, which turns `α_b^n/α_a^n` into `(xs a b)^{-n}`.
-/

namespace Work.C17

/-- The abstract two-sided estimate: for real `A, B, B'` with `B·B' = 1`, `B,B' > 0`, and
sequences `d, u` satisfying the two-sided hypotheses (with the auxiliary constants
`0 < c ≤ C`), the products `d n * u n` are bounded above and below in terms of `A·B'`. -/
private lemma Ffun_two_sided_aux (A B B' c C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hBB' : B * B' = 1) (hc : 0 < c) (hCc : c ≤ C) (d u : ℕ → ℝ)
    (hdlo : ∀ n : ℕ, c / (((n : ℝ) + 1) ^ 4 * A ^ n) ≤ |d n|)
    (hdhi : ∀ n : ℕ, |d n| ≤ C * ((n : ℝ) + 1) ^ 2 / A ^ n)
    (hulo : ∀ n : ℕ, B ^ n / ((n : ℝ) + 1) ≤ u n)
    (huhi : ∀ n : ℕ, u n ≤ B ^ n) (n : ℕ) :
    |d n * u n| ≤ C * ((n : ℝ) + 1) ^ 3 / (A * B') ^ n ∧
      c / (((n : ℝ) + 1) ^ 5 * (A * B') ^ n) ≤ |d n * u n| := by
  have hCpos : 0 < C := lt_of_lt_of_le hc hCc
  have hupos : 0 < u n :=
    lt_of_lt_of_le (show (0 : ℝ) < B ^ n / ((n : ℝ) + 1) by positivity) (hulo n)
  have hkey : B ^ n / A ^ n = ((A * B') ^ n)⁻¹ := by
    have h1 : B ^ n * B' ^ n = 1 := by rw [← mul_pow, hBB', one_pow]
    rw [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_eq_of_mul_eq_one_left h1]
  constructor
  · rw [abs_mul, abs_of_pos hupos]
    calc |d n| * u n ≤ (C * ((n : ℝ) + 1) ^ 2 / A ^ n) * B ^ n :=
          mul_le_mul (hdhi n) (huhi n) (le_of_lt hupos)
            (show (0 : ℝ) ≤ C * ((n : ℝ) + 1) ^ 2 / A ^ n by positivity)
      _ = C * ((n : ℝ) + 1) ^ 2 * (B ^ n / A ^ n) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ C * ((n : ℝ) + 1) ^ 3 * (B ^ n / A ^ n) := by
            have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
            have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 3 := by
              calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
                _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) :=
                    mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = ((n : ℝ) + 1) ^ 3 := by ring
            have hm : C * ((n : ℝ) + 1) ^ 2 ≤ C * ((n : ℝ) + 1) ^ 3 :=
              mul_le_mul_of_nonneg_left hsq (le_of_lt hCpos)
            exact mul_le_mul_of_nonneg_right hm (by positivity)
      _ = C * ((n : ℝ) + 1) ^ 3 / (A * B') ^ n := by rw [hkey, div_eq_mul_inv]
  · rw [abs_mul, abs_of_pos hupos]
    have hprod : (c / (((n : ℝ) + 1) ^ 4 * A ^ n)) * (B ^ n / ((n : ℝ) + 1))
        ≤ |d n| * u n :=
      mul_le_mul (hdlo n) (hulo n) (by positivity) (abs_nonneg _)
    have key : c / (((n : ℝ) + 1) ^ 5 * (A * B') ^ n)
        = (c / (((n : ℝ) + 1) ^ 4 * A ^ n)) * (B ^ n / ((n : ℝ) + 1)) := by
      have h1 : B ^ n * B' ^ n = 1 := by rw [← mul_pow, hBB', one_pow]
      have hkey1 : c / (((n : ℝ) + 1) ^ 5 * (A * B') ^ n)
          = c * B ^ n / (((n : ℝ) + 1) ^ 5 * A ^ n) := by
        simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, inv_eq_of_mul_eq_one_left h1]
        ring
      have hkey2 : (c / (((n : ℝ) + 1) ^ 4 * A ^ n)) * (B ^ n / ((n : ℝ) + 1))
          = c * B ^ n / (((n : ℝ) + 1) ^ 5 * A ^ n) := by
        rw [div_mul_div_comm]
        congr 1
        ring
      rw [hkey1, hkey2]
    rw [key]
    exact hprod

theorem Ffun_two_sided (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (c C : ℝ) (hc : 0 < c)
    (hdalo : ∀ n : ℕ, c / (((n : ℝ) + 1) ^ 4 * ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
        ≤ |Submission.CDT.beukersD (a : ℝ) n|)
    (hdahi : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
    (hublo : ∀ n : ℕ, ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n / ((n : ℝ) + 1)
        ≤ Submission.CDT.beukersUR (b : ℝ) n)
    (hubhi : ∀ n : ℕ, Submission.CDT.beukersUR (b : ℝ) n
        ≤ ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n) :
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, |Ffun a b n| ≤ C₁ * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ n : ℕ,
        c₁ / (((n : ℝ) + 1) ^ 5 * (xs a b) ^ n) ≤ |Ffun a b n|) := by
  have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hsb : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hApos : 0 < (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) := by
    have := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1); linarith
  have hBpos : 0 < (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    have := Real.sqrt_nonneg ((b : ℝ) ^ 2 - 1); linarith
  have hBB' : ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1))
      * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) = 1 := by nlinarith [hsb]
  have hle1 : c ≤ |Submission.CDT.beukersD (a : ℝ) 0| := by
    have := hdalo 0; simpa using this
  have hle2 : |Submission.CDT.beukersD (a : ℝ) 0| ≤ C := by
    have := hdahi 0; simpa using this
  have hcc : c ≤ C := le_trans hle1 hle2
  have hCpos : 0 < C := lt_of_lt_of_le hc hcc
  have hmain : ∀ n : ℕ,
      |Ffun a b n| ≤ C * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n ∧
        c / (((n : ℝ) + 1) ^ 5 * (xs a b) ^ n) ≤ |Ffun a b n| := by
    intro n
    have h := Ffun_two_sided_aux ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1))
      ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1))
      ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) c C hApos hBpos hBB' hc hcc
      (fun n => Submission.CDT.beukersD (a : ℝ) n)
      (fun n => Submission.CDT.beukersUR (b : ℝ) n) hdalo hdahi hublo hubhi n
    simpa [Ffun, xs] using h
  exact ⟨⟨C, hCpos, fun n => (hmain n).1⟩, ⟨c, hc, fun n => (hmain n).2⟩⟩

end Work.C17
