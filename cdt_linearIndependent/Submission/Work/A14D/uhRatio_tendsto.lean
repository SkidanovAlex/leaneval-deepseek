import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.uhCoeff_bound

/-!
# A14D — `a_{n+1}/a_n → 9/8` for the coefficients of the holomorphic solution `u_h`

`uhCoeff : ℕ → ℚ` are the coefficients of the holomorphic solution `u_h` of the Zagier operator
`L` at `x = 1` (`Submission.Work.A14.defs`): `a_0 = 1`, `a_1 = 3/4`, and

  `a_{k+2} = ((17 (k+1) (k+2) + 6) a_{k+1} - 9 (k+1)² a_k) / (8 (k+2)²)`.

`Submission.Work.A14D.uhCoeff_bound` proves `0 < a_n`, `a_{n+1} ≤ (9/8) a_n` and the geometric
lower bound `a_8 (101/100)^n ≤ a_{n+8}`.  Here we sharpen this to the *convergence of the ratio*:

  `a_{n+1}/a_n → 9/8`   (equivalently, `9/8` is the reciprocal of the radius of convergence).

The proof is an elementary contraction estimate.  Writing `R n = a_{n+1}/a_n` and
`δ n = 9/8 − R n`, dividing the recurrence by `a_{n+1}` gives the forward recursion

  `R (n+1) = F_{n+1}(R n)`,   `F_m(t) = (17 m (m+1) + 6 − 9 m²/t) / (8 (m+1)²)`,

and an explicit computation (with `m = n+1`) shows

  `δ (n+1) = (m+3)/(8 (m+1)²) + (m/(m+1))² · δ n / R n`.

Since `101/100 ≤ R n ≤ 9/8` for `n ≥ 8` we have `δ n / R n ≤ (100/101) δ n`, so `δ` obeys the
linear recurrence

  `δ (n+1) ≤ (n+4)/(8 (n+2)²) + ((n+1)/(n+2))² · (100/101) · δ n`,

whose companion matrix has `∏_{k<n} ((k+1)/(k+2))² = (9/(n+1))² → 0` and whose inhomogeneity
contributes the geometric factor `(100/101)^{n-k}`; the result is the explicit bound
`0 ≤ δ n ≤ 20/(n+1)` for `n ≥ 8`, proved by a one-step induction (`δ n ≤ 20/(n+1) ⟹
δ (n+1) ≤ 20/(n+2)`, using only `m ≥ 1`).  This is more than enough for the ε–N statement.
-/

open Filter
open scoped Topology

namespace Work.A14D

noncomputable section

/-- The ratio `R n = a_{n+1}/a_n` of consecutive coefficients of `uh`, as a real number. -/
def uhR (n : ℕ) : ℝ := (uhCoeff (n + 1) : ℝ) / (uhCoeff n : ℝ)

/-- The deficit `δ n = 9/8 − R n`. -/
def uhDelta (n : ℕ) : ℝ := 9 / 8 - uhR n

/-- The one-step map of the ratio recursion: `F_m(t) = (17 m (m+1) + 6 − 9 m²/t)/(8 (m+1)²)`. -/
def uhStep (m t : ℝ) : ℝ := (17 * m * (m + 1) + 6 - 9 * m ^ 2 / t) / (8 * (m + 1) ^ 2)

lemma uhCoeffPosR (n : ℕ) : (0 : ℝ) < (uhCoeff n : ℝ) := by
  have := (uhCoeff_bound.1 n); exact_mod_cast this

lemma uhR_pos (n : ℕ) : 0 < uhR n := div_pos (uhCoeffPosR _) (uhCoeffPosR _)

/-- The upper bound `a_{n+1} ≤ (9/8) a_n` of `uhCoeff_bound`, cast to `ℝ` and divided. -/
lemma uhR_le (n : ℕ) : uhR n ≤ 9 / 8 := by
  have h : (uhCoeff (n + 1) : ℝ) ≤ (9 / 8 : ℝ) * (uhCoeff n : ℝ) := by
    have h0 := (uhCoeff_bound.2.1) n
    have h1 : ((uhCoeff (n + 1) : ℚ) : ℝ) ≤ (((9 / 8 : ℚ) * uhCoeff n : ℚ) : ℝ) := by
      exact_mod_cast h0
    push_cast at h1
    simpa using h1
  rw [uhR, div_le_iff₀ (uhCoeffPosR n)]
  exact h

/-- The forward recursion for the ratio, obtained by dividing the defining recurrence of
`uhCoeff` by `a_{n+1}`. -/
lemma uhR_succ (n : ℕ) : uhR (n + 1) = uhStep ((n : ℝ) + 1) (uhR n) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (uhCoeff.eq_3 n)
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_natCast] at h
  rw [uhR, h, uhR, uhStep]
  have hn : (uhCoeff n : ℝ) ≠ 0 := ne_of_gt (uhCoeffPosR n)
  have hn1 : (uhCoeff (n + 1) : ℝ) ≠ 0 := ne_of_gt (uhCoeffPosR (n + 1))
  field_simp
  ring

/-- The explicit identity for the deficit: `9/8 − F_m(t) = (m+3)/(8(m+1)²) + (m/(m+1))²·(9/8−t)/t`. -/
lemma uhStep_delta (m t : ℝ) (ht : t ≠ 0) (hm : m + 1 ≠ 0) :
    9 / 8 - uhStep m t
      = (m + 3) / (8 * (m + 1) ^ 2) + (m / (m + 1)) ^ 2 * ((9 / 8 - t) / t) := by
  rw [uhStep]
  field_simp
  ring

/-- One step of the lower bound: if `8 ≤ m` and `t ≥ 101/100` then `F_m(t) ≥ 101/100`. -/
lemma uhStep_low (m : ℝ) (hm : 8 ≤ m) {t : ℝ} (ht : (101 : ℝ) / 100 ≤ t) :
    (101 : ℝ) / 100 ≤ uhStep m t := by
  rw [uhStep]
  have ht0 : (0 : ℝ) < t := by linarith
  have hden : (0 : ℝ) < 8 * (m + 1) ^ 2 := by positivity
  have h9 : 9 * m ^ 2 / t ≤ 900 * m ^ 2 / 101 := by
    rw [div_le_iff₀ ht0]
    nlinarith [mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 900 * m ^ 2 / 101 by positivity)]
  have hnum : 17 * m * (m + 1) + 6 - 900 * m ^ 2 / 101
      ≤ 17 * m * (m + 1) + 6 - 9 * m ^ 2 / t := by linarith
  calc (101 : ℝ) / 100
      ≤ (17 * m * (m + 1) + 6 - 900 * m ^ 2 / 101) / (8 * (m + 1) ^ 2) := by
        rw [le_div_iff₀ hden]
        nlinarith [sq_nonneg (m - 8)]
    _ ≤ (17 * m * (m + 1) + 6 - 9 * m ^ 2 / t) / (8 * (m + 1) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)

/-- From index `8` on the ratio is at least `101/100`. -/
lemma uhR_ge : ∀ n : ℕ, 8 ≤ n → (101 : ℝ) / 100 ≤ uhR n := by
  apply Nat.le_induction
  · have h := (uhCoeff_bound.2.2) 1
    have h1 : ((uhCoeff 8 * (101 / 100) ^ 1 : ℚ) : ℝ) ≤ ((uhCoeff (1 + 8) : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at h1
    simp only [pow_one] at h1
    rw [uhR, le_div_iff₀ (uhCoeffPosR 8)]
    linarith
  · intro k hk ih
    rw [uhR_succ k]
    apply uhStep_low ((k : ℝ) + 1)
    · have : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    · exact ih

/-- The deficit recursion: `δ (n+1) = F`-formula with `m = n+1`. -/
lemma uhDelta_succ (n : ℕ) :
    uhDelta (n + 1) = (((n : ℝ) + 1) + 3) / (8 * (((n : ℝ) + 1) + 1) ^ 2)
      + (((n : ℝ) + 1) / (((n : ℝ) + 1) + 1)) ^ 2 * (uhDelta n / uhR n) := by
  rw [uhDelta, uhR_succ n,
    uhStep_delta ((n : ℝ) + 1) (uhR n) (ne_of_gt (uhR_pos n)) (by positivity), uhDelta]

/-- A one-step numerical inequality: the bound `δ n ≤ K/m` with `K = 20` propagates
(`m = n+1 ≥ 1`). -/
lemma uhStep_bound {m : ℝ} (hm : 0 < m) :
    (m + 3) / (8 * (m + 1) ^ 2) + (m / (m + 1)) ^ 2 * (((100 : ℝ) / 101) * (20 / m))
      ≤ 20 / (m + 1) := by
  have hL : (m + 3) / (8 * (m + 1) ^ 2) + (m / (m + 1)) ^ 2 * (((100 : ℝ) / 101) * (20 / m))
      = ((m + 3) / 8 + 2000 * m / 101) / (m + 1) ^ 2 := by
    field_simp
    ring
  rw [hL, div_le_iff₀ (by positivity : (0 : ℝ) < (m + 1) ^ 2)]
  have h20 : 20 / (m + 1) * (m + 1) ^ 2 = 20 * (m + 1) := by field_simp
  rw [h20]
  have h2 : (m + 3) / 8 + 2000 * m / 101 = (101 * (m + 3) + 16000 * m) / 808 := by
    field_simp
    ring
  rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 808)]
  linarith

/-- The explicit decay bound for the deficit: `0 ≤ δ n ≤ 20/(n+1)` for `n ≥ 8`. -/
lemma uhDelta_bound : ∀ n : ℕ, 8 ≤ n → 0 ≤ uhDelta n ∧ uhDelta n ≤ 20 / ((n : ℝ) + 1) := by
  apply Nat.le_induction
  · refine ⟨sub_nonneg.mpr (uhR_le 8), ?_⟩
    have hle : uhDelta 8 ≤ 9 / 8 := by rw [uhDelta]; linarith [uhR_pos 8]
    have h2 : (9 : ℝ) / 8 ≤ 20 / (((8 : ℕ) : ℝ) + 1) := by norm_num
    linarith
  · intro k hk ih
    obtain ⟨ih0, ih1⟩ := ih
    push_cast
    refine ⟨sub_nonneg.mpr (uhR_le (k + 1)), ?_⟩
    rw [uhDelta_succ k]
    have hm : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiv : uhDelta k / uhR k ≤ ((100 : ℝ) / 101) * uhDelta k := by
      rw [div_le_iff₀ (uhR_pos k)]
      have hR101 : (101 : ℝ) / 100 ≤ uhR k := uhR_ge k hk
      nlinarith [ih0, uhR_pos k, hR101]
    have hsq : (0 : ℝ) ≤ (((k : ℝ) + 1) / (((k : ℝ) + 1) + 1)) ^ 2 := by positivity
    have hstep1 : (((k : ℝ) + 1) / (((k : ℝ) + 1) + 1)) ^ 2 * (uhDelta k / uhR k)
        ≤ (((k : ℝ) + 1) / (((k : ℝ) + 1) + 1)) ^ 2
            * (((100 : ℝ) / 101) * (20 / ((k : ℝ) + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hsq
      calc uhDelta k / uhR k ≤ ((100 : ℝ) / 101) * uhDelta k := hdiv
        _ ≤ ((100 : ℝ) / 101) * (20 / ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left ih1 (by norm_num)
    calc (((k : ℝ) + 1) + 3) / (8 * (((k : ℝ) + 1) + 1) ^ 2)
            + (((k : ℝ) + 1) / (((k : ℝ) + 1) + 1)) ^ 2 * (uhDelta k / uhR k)
        ≤ (((k : ℝ) + 1) + 3) / (8 * (((k : ℝ) + 1) + 1) ^ 2)
            + (((k : ℝ) + 1) / (((k : ℝ) + 1) + 1)) ^ 2
                * (((100 : ℝ) / 101) * (20 / ((k : ℝ) + 1))) := by
          linarith [hstep1]
      _ ≤ 20 / (((k : ℝ) + 1) + 1) := uhStep_bound hm

theorem uhRatio_tendsto :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |(uhCoeff (n + 1) : ℝ) / (uhCoeff n : ℝ) - 9 / 8| < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (20 / ε)
  refine ⟨max M 8, fun n hn => ?_⟩
  have hn8 : 8 ≤ n := le_trans (le_max_right M 8) hn
  have hMn : M ≤ n := le_trans (le_max_left M 8) hn
  have hb := uhDelta_bound n hn8
  have hbnd : (20 : ℝ) / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have h1 : (20 : ℝ) / ε < (n : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hMn)
    have h2 : (20 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    nlinarith [hε, h2]
  have hgoal : |uhR n - 9 / 8| < ε := by
    have he : uhR n - 9 / 8 = -(uhDelta n) := by rw [uhDelta]; ring
    rw [he, abs_neg, abs_of_nonneg hb.1]
    linarith [hb.2, hbnd]
  exact hgoal

end

end Work.A14D
