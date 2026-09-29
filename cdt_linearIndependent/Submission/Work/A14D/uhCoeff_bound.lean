import Mathlib
import Submission.Work.A14.defs

/-!
# Bounds for the coefficients `uhCoeff`

`uhCoeff : ℕ → ℚ` is the sequence of coefficients of the holomorphic solution `u_h` of the
Zagier operator `L` at `x = 1` (`Work.A14D.uh`): `a_0 = 1`, `a_1 = 3/4`, and
`a_{k+2} = ((17(k+1)(k+2)+6) a_{k+1} - 9(k+1)² a_k) / (8 (k+2)²)`.

We show (`Work.A14D.uhCoeff_bound`)

* `0 < a_n` for all `n`;
* `a_{n+1} ≤ 9/8 · a_n` for all `n` (so the series `Σ a_n (1−z)^n` converges on `|1−z| < 8/9`);
* `a_8 · (101/100)^n ≤ a_{n+8}` for all `n` (a geometric lower bound from index `8` on).

The whole argument is carried out on the ratio `R n = a_{n+1} / a_n`.  From the three-term
recurrence, `R` satisfies the (forward) recursion
`R (n+1) = (17 m (m+1) + 6 - 9 m² / R n) / (8 (m+1)²)` with `m = n+1`; the right-hand side is
increasing in `R n` (for `R n > 0`), so an upper bound propagates, and once we know `R n ≥ 101/100`
for `n ≥ 8` (checked directly at `n = 8` and propagated, using that the right-hand side at the
lower bound `101/100` is again `≥ 101/100` for `m ≥ 8`), the geometric lower bound follows.
-/

noncomputable section

namespace Work.A14D

/-- The ratio `R n = uhCoeff (n+1) / uhCoeff n` of consecutive coefficients. -/
private def uhRatio (n : ℕ) : ℚ := uhCoeff (n + 1) / uhCoeff n

private lemma uhRatio_zero : uhRatio 0 = 3 / 4 := by simp [uhRatio, uhCoeff]

/-- The forward recursion for the ratio, obtained from the defining recurrence of `uhCoeff`. -/
private lemma uhRatio_succ (n : ℕ) (_hn : uhCoeff n ≠ 0) (hn1 : uhCoeff (n + 1) ≠ 0) :
    uhRatio (n + 1) =
      (17 * ((n : ℚ) + 1) * (((n : ℚ) + 1) + 1) + 6 - 9 * ((n : ℚ) + 1) ^ 2 / uhRatio n)
        / (8 * (((n : ℚ) + 1) + 1) ^ 2) := by
  simp only [uhRatio]
  rw [uhCoeff.eq_3 n]
  field_simp
  ring

/-- Upper bound for one step of the ratio recursion: if `0 < t ≤ 9/8` and `1 ≤ m` then
`F t ≤ 9/8`. -/
private lemma ratio_step_le (m : ℚ) (hm : 1 ≤ m) {t : ℚ} (ht : 0 < t) (hle : t ≤ 9 / 8) :
    (17 * m * (m + 1) + 6 - 9 * m ^ 2 / t) / (8 * (m + 1) ^ 2) ≤ 9 / 8 := by
  have hden : (0 : ℚ) < 8 * (m + 1) ^ 2 := by positivity
  have h9 : 8 * m ^ 2 ≤ 9 * m ^ 2 / t := by
    rw [le_div_iff₀ ht]
    nlinarith [mul_le_mul_of_nonneg_left hle (show (0 : ℚ) ≤ 8 * m ^ 2 by positivity)]
  rw [div_le_iff₀ hden]
  nlinarith [h9]

/-- Lower bound for one step of the ratio recursion: if `101/100 ≤ t` and `8 ≤ m` then
`101/100 ≤ F t`. -/
private lemma ratio_step_low (m : ℚ) (hm : 8 ≤ m) {t : ℚ} (ht : 101 / 100 ≤ t) :
    101 / 100 ≤ (17 * m * (m + 1) + 6 - 9 * m ^ 2 / t) / (8 * (m + 1) ^ 2) := by
  have ht0 : (0 : ℚ) < t := by linarith
  have hden : (0 : ℚ) < 8 * (m + 1) ^ 2 := by positivity
  have h9 : 9 * m ^ 2 / t ≤ 900 * m ^ 2 / 101 := by
    rw [div_le_iff₀ ht0]
    nlinarith [mul_le_mul_of_nonneg_left ht (show (0 : ℚ) ≤ 900 * m ^ 2 / 101 by positivity)]
  have hnum : 17 * m * (m + 1) + 6 - 900 * m ^ 2 / 101 ≤ 17 * m * (m + 1) + 6 - 9 * m ^ 2 / t :=
    by linarith
  calc (101 : ℚ) / 100 ≤ (17 * m * (m + 1) + 6 - 900 * m ^ 2 / 101) / (8 * (m + 1) ^ 2) := by
        rw [le_div_iff₀ hden]
        nlinarith [sq_nonneg (m - 8)]
    _ ≤ (17 * m * (m + 1) + 6 - 9 * m ^ 2 / t) / (8 * (m + 1) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)

/-- From index `8` on, the ratio is at least `101/100` (and at most `9/8`). -/
private lemma uhRatio_ge : ∀ n, 8 ≤ n → 101 / 100 ≤ uhRatio n ∧ uhRatio n ≤ 9 / 8 := by
  apply Nat.le_induction
  · constructor <;> norm_num [uhRatio, uhCoeff]
  · intro n hn ih
    obtain ⟨hlow, hup⟩ := ih
    have hnz : uhCoeff n ≠ 0 := by
      intro h
      rw [uhRatio, h, div_zero] at hlow
      linarith
    have hn1z : uhCoeff (n + 1) ≠ 0 := by
      intro h
      rw [uhRatio, h, zero_div] at hlow
      linarith
    rw [uhRatio_succ n hnz hn1z]
    have h8 : (8 : ℚ) ≤ ((n : ℚ) + 1) := by
      have h : (8 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      linarith
    have h1 : (1 : ℚ) ≤ ((n : ℚ) + 1) := by
      have h : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
      linarith
    exact ⟨ratio_step_low ((n : ℚ) + 1) h8 hlow,
      ratio_step_le ((n : ℚ) + 1) h1 (by linarith) hup⟩

/-- For `n ≤ 8` the ratio's bounds are checked by direct computation. -/
private lemma uhRatio_small : ∀ n ≤ 8, 0 < uhRatio n ∧ uhRatio n ≤ 9 / 8 := by
  intro n hn
  interval_cases n <;> constructor <;> norm_num [uhRatio, uhCoeff]

/-- The ratio is always positive and at most `9/8`. -/
private lemma uhRatio_bounds (n : ℕ) : 0 < uhRatio n ∧ uhRatio n ≤ 9 / 8 := by
  by_cases h : n ≤ 8
  · exact uhRatio_small n h
  · rw [not_le] at h
    have hh := uhRatio_ge n (by omega)
    exact ⟨by linarith [hh.1], hh.2⟩

/-- All coefficients are positive. -/
private lemma uhCoeff_pos (n : ℕ) : 0 < uhCoeff n := by
  induction n with
  | zero => rw [uhCoeff.eq_1]; norm_num
  | succ n ih =>
    have hne : uhCoeff n ≠ 0 := ne_of_gt ih
    have hmul : uhRatio n * uhCoeff n = uhCoeff (n + 1) := by
      rw [uhRatio]
      exact div_mul_cancel₀ _ hne
    rw [← hmul]
    exact mul_pos (uhRatio_bounds n).1 ih

theorem uhCoeff_bound : (∀ n : ℕ, 0 < uhCoeff n) ∧ (∀ n : ℕ, uhCoeff (n + 1) ≤ 9 / 8 * uhCoeff n) ∧ (∀ n : ℕ, uhCoeff 8 * (101 / 100) ^ n ≤ uhCoeff (n + 8)) := by
  refine ⟨uhCoeff_pos, ?_, ?_⟩
  · intro n
    have hne : uhCoeff n ≠ 0 := ne_of_gt (uhCoeff_pos n)
    have hmul : uhRatio n * uhCoeff n = uhCoeff (n + 1) := by
      rw [uhRatio]; exact div_mul_cancel₀ _ hne
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (uhRatio_bounds n).2 (le_of_lt (uhCoeff_pos n))
  · intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hne : uhCoeff (k + 8) ≠ 0 := ne_of_gt (uhCoeff_pos (k + 8))
      have hmul : uhRatio (k + 8) * uhCoeff (k + 8) = uhCoeff (k + 8 + 1) := by
        rw [uhRatio]; exact div_mul_cancel₀ _ hne
      have hR : (101 / 100 : ℚ) ≤ uhRatio (k + 8) := (uhRatio_ge (k + 8) (by omega)).1
      calc uhCoeff 8 * (101 / 100) ^ (k + 1)
          = uhCoeff 8 * (101 / 100) ^ k * (101 / 100) := by rw [pow_succ]; ring
        _ ≤ uhCoeff (k + 8) * (101 / 100) := mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ uhCoeff (k + 8) * uhRatio (k + 8) :=
            mul_le_mul_of_nonneg_left hR (le_of_lt (uhCoeff_pos (k + 8)))
        _ = uhRatio (k + 8) * uhCoeff (k + 8) := by ring
        _ = uhCoeff (k + 1 + 8) := by rw [hmul]

end Work.A14D
