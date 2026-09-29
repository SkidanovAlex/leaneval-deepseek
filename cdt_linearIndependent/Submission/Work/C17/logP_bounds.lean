import Mathlib
import Submission.Work.C17.logP_defs
import Submission.Work.C17.Ffun_two_sided
import Submission.Work.C17.Kfun_bound

namespace Work.C17

/-- For `3 ≤ a < b` the Taylor radius `xs a b = (a+√(a²−1))·(b−√(b²−1))` of the unlikely
series lies in `(0,1)`. -/
theorem xs_pos_and_sq_lt_one (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b) :
    0 < xs a b ∧ xs a b * xs a b < 1 := by
  have haR : (1:ℝ) ≤ (a:ℝ) := by
    have h : (3:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    linarith
  have hbR : (1:ℝ) ≤ (b:ℝ) := by
    have h : (3:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith
  have habR : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
  set A : ℝ := (a:ℝ) + Real.sqrt ((a:ℝ)^2 - 1) with hA
  set B : ℝ := (b:ℝ) + Real.sqrt ((b:ℝ)^2 - 1) with hB
  have hsqa : Real.sqrt ((a:ℝ)^2 - 1)^2 = (a:ℝ)^2 - 1 := Real.sq_sqrt (by nlinarith)
  have hsqb : Real.sqrt ((b:ℝ)^2 - 1)^2 = (b:ℝ)^2 - 1 := Real.sq_sqrt (by nlinarith)
  have hApos : 0 < A := by
    rw [hA]
    have hs := Real.sqrt_nonneg ((a:ℝ)^2 - 1)
    have ha0 : (0:ℝ) < (a:ℝ) := by linarith
    linarith
  have hBpos : 0 < B := by
    rw [hB]
    have hs := Real.sqrt_nonneg ((b:ℝ)^2 - 1)
    have hb0 : (0:ℝ) < (b:ℝ) := by linarith
    linarith
  have hBβ : B * ((b:ℝ) - Real.sqrt ((b:ℝ)^2 - 1)) = 1 := by
    rw [hB]; nlinarith
  have hxs_eq : xs a b = A * ((b:ℝ) - Real.sqrt ((b:ℝ)^2 - 1)) := by
    rw [xs, ← hA]
  have hβb : (b:ℝ) - Real.sqrt ((b:ℝ)^2 - 1) = 1/B := by
    rw [eq_div_iff (ne_of_gt hBpos)]
    rw [mul_comm]; exact hBβ
  have hxsB : xs a b = A / B := by rw [hxs_eq, hβb]; ring
  have hAltB : A < B := by
    rw [hA, hB]
    have hs : Real.sqrt ((a:ℝ)^2 - 1) < Real.sqrt ((b:ℝ)^2 - 1) := by
      apply Real.sqrt_lt_sqrt
      · nlinarith
      · nlinarith
    linarith
  have hxs_pos : 0 < xs a b := by rw [hxsB]; positivity
  have hxs_lt1 : xs a b < 1 := by
    rw [hxsB, div_lt_one hBpos]; exact hAltB
  refine ⟨hxs_pos, ?_⟩
  nlinarith [hxs_pos, hxs_lt1]

theorem logP_bounds (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (ra rb rab : ℤ) (c C : ℝ) (hc : 0 < c)
    (hdalo : ∀ n : ℕ, c / (((n : ℝ) + 1) ^ 4 * ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
        ≤ |Submission.CDT.beukersD (a : ℝ) n|)
    (hdahi : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
    (hdbhi : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n|
        ≤ C * ((n : ℝ) + 1) ^ 2 / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n)
    (huahi : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n
        ≤ ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
    (hublo : ∀ n : ℕ, ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n / ((n : ℝ) + 1)
        ≤ Submission.CDT.beukersUR (b : ℝ) n)
    (hubhi : ∀ n : ℕ, Submission.CDT.beukersUR (b : ℝ) n
        ≤ ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n) :
    0 < xs a b ∧ xs a b * xs a b < 1 ∧
      (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, |Ffun a b n| ≤ C₁ * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ n : ℕ,
        c₁ / (((n : ℝ) + 1) ^ 5 * (xs a b) ^ n) ≤ |Ffun a b n|) ∧
      (∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ,
        |Kfun a b ra rb rab n| ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n) := by
  have hxs := xs_pos_and_sq_lt_one a b ha hb hab
  have hCpos : 0 < C := by
    have h1 := hdahi 0
    have h2 := hdalo 0
    simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one, div_one] at h1 h2
    linarith
  have hF := Ffun_two_sided a b ha hb c C hc hdalo hdahi hublo hubhi
  have hK := Kfun_bound a b ha hb ra rb rab C hCpos hdahi hdbhi huahi
  exact ⟨hxs.1, hxs.2, hF.1, hF.2, hK⟩

end Work.C17
