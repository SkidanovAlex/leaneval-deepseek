import Mathlib
import Submission.Work.NN.Final.MomentSetup

/-!
# Positivity of the Seeley normalising constant

`mkappa = ∑' n, mcoef n = ∏_{p ≥ 1} (1 - 3^{-p})` is the normalising constant of the
Seeley moment construction.  We prove here that it is positive, indeed that
`1/2 ≤ mkappa` (numerically `mkappa ≈ 0.5601`).

The coefficients `mcoef` alternate in sign and decrease in absolute value:

* `mcoef (n+1) = -(mcoef n)/(3^(n+1) - 1)`, so `|mcoef (n+1)| ≤ |mcoef n|`;
* `(-1)^n * mcoef n = |mcoef n|`, so the sign of `mcoef n` is `(-1)^n`.

Consequently the even partial sums `∑_{n < 2m} mcoef n` are increasing: from a pair of
consecutive indices `(2k, 2k+1)` the contribution is `|mcoef 2k| - |mcoef (2k+1)| ≥ 0`.
Since the partial sum up to `2` already equals `1 - 1/2 = 1/2`, every partial sum of
length `≥ 2` is `≥ 1/2`, and passing to the limit gives `1/2 ≤ mkappa`.
-/

namespace Work.NN.Final

/-- The recurrence in absolute values: `|mcoef (n+1)| = |mcoef n| / (3^{n+1} - 1)`. -/
lemma mcoef_abs_succ (n : ℕ) : |mcoef (n+1)| = |mcoef n| / ((3:ℝ)^(n+1) - 1) := by
  have hD : (0:ℝ) < (3:ℝ)^(n+1) - 1 := by
    have h := three_pow_ge_real n
    have : (0:ℝ) < 2*(n+1) := by positivity
    linarith
  rw [mcoef_succ, abs_div, abs_neg, abs_of_pos hD]

/-- The sign of `mcoef n` is `(-1)^n`: `(-1)^n * mcoef n = |mcoef n|`. -/
lemma mcoef_signed (n : ℕ) : (-1:ℝ)^n * mcoef n = |mcoef n| := by
  induction n with
  | zero => norm_num [mcoef]
  | succ k ih =>
    have hD : (3:ℝ)^(k+1) - 1 ≠ 0 := by
      have h := three_pow_ge_real k
      have : (0:ℝ) < 2*(k+1) := by positivity
      linarith
    have key : (-1:ℝ)^(k+1) * (-(mcoef k) / ((3:ℝ)^(k+1)-1))
        = ((-1:ℝ)^k * mcoef k) / ((3:ℝ)^(k+1)-1) := by ring
    rw [mcoef_abs_succ k, mcoef_succ, key, ih]

/-- The absolute values of `mcoef` are non-increasing. -/
lemma mcoef_abs_mono (n : ℕ) : |mcoef (n+1)| ≤ |mcoef n| := by
  rw [mcoef_abs_succ]
  have hD : (0:ℝ) < (3:ℝ)^(n+1) - 1 := by
    have h := three_pow_ge_real n
    have : (0:ℝ) < 2*(n+1) := by positivity
    linarith
  have h2 : (1:ℝ) ≤ (3:ℝ)^(n+1) - 1 := by
    have h := three_pow_ge_real n
    have : (0:ℝ) < 2*(n+1) := by positivity
    linarith
  rw [div_le_iff₀ hD]
  nlinarith [abs_nonneg (mcoef n)]

/-- The even-indexed coefficients are non-negative. -/
lemma mcoef_even_nonneg (k : ℕ) : 0 ≤ mcoef (2*k) := by
  have h := mcoef_signed (2*k)
  rw [Even.neg_one_pow (even_two_mul k), one_mul] at h
  rw [h]
  exact abs_nonneg _

/-- Even-indexed coefficients equal their absolute values. -/
lemma mcoef_even_abs (k : ℕ) : mcoef (2*k) = |mcoef (2*k)| := by
  have h := mcoef_signed (2*k)
  rw [Even.neg_one_pow (even_two_mul k), one_mul] at h
  exact h

/-- Odd-indexed coefficients are the negatives of their absolute values. -/
lemma mcoef_odd_abs (k : ℕ) : mcoef (2*k+1) = -|mcoef (2*k+1)| := by
  have h := mcoef_signed (2*k+1)
  rw [Odd.neg_one_pow (show Odd (2*k+1) from ⟨k, rfl⟩), neg_one_mul] at h
  linarith

/-- Each pair of consecutive coefficients starting at an even index has non-negative sum. -/
lemma mcoef_pair_nonneg (k : ℕ) : 0 ≤ mcoef (2*k) + mcoef (2*k+1) := by
  have h3 : |mcoef (2*k+1)| ≤ |mcoef (2*k)| := mcoef_abs_mono (2*k)
  rw [mcoef_even_abs, mcoef_odd_abs]
  linarith

/-- The partial sum of even length, written as a sum of pairs. -/
lemma mcoef_sum_range_two_mul (m : ℕ) :
    ∑ n ∈ Finset.range (2*m), mcoef n
      = ∑ k ∈ Finset.range m, (mcoef (2*k) + mcoef (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m + 1 + 1 from by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Every even partial sum of length `≥ 2` is at least `1/2`. -/
lemma mcoef_even_partial_ge (m : ℕ) : (1/2 : ℝ) ≤ ∑ n ∈ Finset.range (2*m + 2), mcoef n := by
  rw [show 2*m + 2 = 2*(m+1) from by ring, mcoef_sum_range_two_mul, Finset.sum_range_succ']
  have h0 : mcoef (2*0) + mcoef (2*0+1) = (1/2:ℝ) := by norm_num [mcoef, mcoef_succ]
  have hnn : 0 ≤ ∑ k ∈ Finset.range m, (mcoef (2*(k+1)) + mcoef (2*(k+1)+1)) :=
    Finset.sum_nonneg (fun k _ => mcoef_pair_nonneg (k+1))
  linarith

/-- Every partial sum of length `≥ 2` is at least `1/2`. -/
lemma mcoef_partial_ge (N : ℕ) (hN : 2 ≤ N) : (1/2 : ℝ) ≤ ∑ n ∈ Finset.range N, mcoef n := by
  rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm1 : 1 ≤ m := by omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm, show (m'+1) + (m'+1) = 2*m' + 2 from by ring]
    exact mcoef_even_partial_ge m'
  · have hm1 : 1 ≤ m := by omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm, show 2*(m'+1) + 1 = (2*m' + 2) + 1 from by ring, Finset.sum_range_succ]
    have h1 := mcoef_even_partial_ge m'
    have h2 : 0 ≤ mcoef (2*m' + 2) := by
      have := mcoef_even_nonneg (m'+1)
      simpa [show 2*(m'+1) = 2*m' + 2 from by ring] using this
    linarith

/-- The normalising constant `mkappa = ∑' n, mcoef n = ∏_{p ≥ 1} (1 - 3^{-p})` is positive. -/
theorem mkappa_pos : 0 < mkappa := by
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, mcoef n) Filter.atTop (nhds mkappa) :=
    mkappa_summable.hasSum.tendsto_sum_nat
  have hconst : Filter.Tendsto (fun _ : ℕ => (1/2:ℝ)) Filter.atTop (nhds (1/2:ℝ)) :=
    tendsto_const_nhds
  have hle : (1/2:ℝ) ≤ mkappa :=
    le_of_tendsto_of_tendsto hconst hlim
      (Filter.eventually_atTop.mpr ⟨2, fun N hN => mcoef_partial_ge N hN⟩)
  linarith

end Work.NN.Final
