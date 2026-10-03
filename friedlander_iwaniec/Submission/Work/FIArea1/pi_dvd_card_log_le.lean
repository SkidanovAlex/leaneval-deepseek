import Mathlib
import Submission.Work.FIArea1.QboxDefs
import Submission.Work.FIArea1.gauss_prime_dvd_card_le

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The two elementary inputs of the dyadic-range count

The proof of `pi_dvd_card_log_le` splits according to the size of `q`:

* `1 ≤ q < 2`: every `π ∈ PiDvd q N W` has `2 ≤ |π|² ≤ 2q < 4`, and `|π|² = 3` is impossible (a
  sum of two squares is never `3`), so `|π|² = 2` and `π` is one of the four elements `±1 ± i`.
  Hence at most `4` primes — `piDvd_card_le_four_of_lt_two`, with the classification of the
  Gaussian integers of norm `2` here.
* `2 ≤ q`: `Work.FIArea1.gauss_prime_dvd_card_le` gives `♯S ≤ 4(1 + log|W|²/log q)`, and the
  hypothesis `|W|² ≤ 64Mq ≤ 1024MN` converts this into `≪ log(MN)` — the elementary real
  inequality `piDvd_log_arith_aux`. -/

/-! ### The Gaussian integers of norm `2` -/

/-- `3` is not a sum of two integer squares: `r² ≤ 3` and `s² ≤ 3` force `|r|, |s| ≤ 1`, and
`0, 1, 2 ≠ 3`. -/
lemma gnorm_ne_three (z : GaussianInt) : Work.FIPlan.gnorm z ≠ 3 := by
  intro h
  have hz : z.re ^ 2 + z.im ^ 2 = (3 : ℤ) := by
    have := gnorm_int z
    rw [h] at this
    norm_num at this
    linarith
  have hr : z.re ^ 2 ≤ 3 := by nlinarith [sq_nonneg z.im]
  have hi : z.im ^ 2 ≤ 3 := by nlinarith [sq_nonneg z.re]
  have hr1 : -1 ≤ z.re := by
    have h1 : 4 * z.re ≥ -7 := by nlinarith [sq_nonneg (z.re + 2)]
    omega
  have hr2 : z.re ≤ 1 := by
    have h1 : 4 * z.re ≤ 7 := by nlinarith [sq_nonneg (z.re - 2)]
    omega
  have hi1 : -1 ≤ z.im := by
    have h1 : 4 * z.im ≥ -7 := by nlinarith [sq_nonneg (z.im + 2)]
    omega
  have hi2 : z.im ≤ 1 := by
    have h1 : 4 * z.im ≤ 7 := by nlinarith [sq_nonneg (z.im - 2)]
    omega
  interval_cases z.re <;> interval_cases z.im <;> norm_num at hz

/-- If `|z|² = 2` then `z` has both coordinates of absolute value `1`. -/
lemma gnorm_eq_two_coords {z : GaussianInt} (h : Work.FIPlan.gnorm z = 2) :
    (z.re = 1 ∨ z.re = -1) ∧ (z.im = 1 ∨ z.im = -1) := by
  have hz : z.re ^ 2 + z.im ^ 2 = (2 : ℤ) := by
    have := gnorm_int z
    rw [h] at this
    norm_num at this
    linarith
  have hrz : z.re ^ 2 ≤ 2 := by nlinarith [sq_nonneg z.im]
  have hiz : z.im ^ 2 ≤ 2 := by nlinarith [sq_nonneg z.re]
  have hr1 : -1 ≤ z.re := by
    have h1 : 2 * z.re ≥ -3 := by nlinarith [sq_nonneg (z.re + 1)]
    omega
  have hr2 : z.re ≤ 1 := by
    have h1 : 2 * z.re ≤ 3 := by nlinarith [sq_nonneg (z.re - 1)]
    omega
  have hi1 : -1 ≤ z.im := by
    have h1 : 2 * z.im ≥ -3 := by nlinarith [sq_nonneg (z.im + 1)]
    omega
  have hi2 : z.im ≤ 1 := by
    have h1 : 2 * z.im ≤ 3 := by nlinarith [sq_nonneg (z.im - 1)]
    omega
  constructor
  · have hc : z.re = -1 ∨ z.re = 0 ∨ z.re = 1 := by omega
    rcases hc with hc | hc | hc
    · exact Or.inr hc
    · exfalso
      rw [hc, zero_pow (by norm_num : 2 ≠ 0)] at hz
      interval_cases z.im <;> norm_num at hz
    · exact Or.inl hc
  · have hc : z.im = -1 ∨ z.im = 0 ∨ z.im = 1 := by omega
    rcases hc with hc | hc | hc
    · exact Or.inr hc
    · exfalso
      rw [hc, zero_pow (by norm_num : 2 ≠ 0)] at hz
      interval_cases z.re <;> norm_num at hz
    · exact Or.inl hc

/-- Every Gaussian prime has `|π|² ≥ 2`. -/
lemma gnorm_prime_ge_two {π : GaussianInt} (h : Prime π) : 2 ≤ Work.FIPlan.gnorm π := by
  have h0 : Work.FIPlan.gnorm π ≠ 0 := fun hz => h.ne_zero ((dvdCard_gnorm_eq_zero_iff π).mp hz)
  have h1 : Work.FIPlan.gnorm π ≠ 1 := fun hz => h.not_isUnit (Zsqrtd.norm_eq_one_iff.mp hz)
  omega

/-! ### The small-`q` case -/

/-- **For `1 ≤ q < 2` the dyadic range `(q, 2q]` contains at most the four primes `±1 ± i`.**

A member `π` of `PiDvd q N W` has `2 ≤ |π|² ≤ 2q < 4`; `3` is not a sum of two squares, so
`|π|² = 2` and `π ∈ {1+i, 1-i, -1+i, -1-i}`. -/
lemma piDvd_card_le_four_of_lt_two {q N : ℝ} {W : GaussianInt} (hq1 : 1 ≤ q) (hq2 : q < 2) :
    ((PiDvd q N W).card : ℝ) ≤ 4 := by
  have hsub : PiDvd q N W ⊆ ({⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩} : Finset GaussianInt) := by
    intro π hπ
    rw [PiDvd, Finset.mem_filter] at hπ
    obtain ⟨-, hp, hqπ, h2qπ, -⟩ := hπ
    have hg2 : 2 ≤ Work.FIPlan.gnorm π := gnorm_prime_ge_two hp
    have hg4 : Work.FIPlan.gnorm π < 4 := by
      have h : (Work.FIPlan.gnorm π : ℝ) < 4 := by linarith
      exact_mod_cast h
    have hg3 : Work.FIPlan.gnorm π ≠ 3 := gnorm_ne_three π
    have hg : Work.FIPlan.gnorm π = 2 := by omega
    obtain ⟨h1, h2⟩ := gnorm_eq_two_coords hg
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (Zsqrtd.ext (by simpa using h1) (by simpa using h2))
    · exact Or.inr (Or.inl (Zsqrtd.ext (by simpa using h1) (by simpa using h2)))
    · exact Or.inr (Or.inr (Or.inl (Zsqrtd.ext (by simpa using h1) (by simpa using h2))))
    · exact Or.inr (Or.inr (Or.inr (Zsqrtd.ext (by simpa using h1) (by simpa using h2))))
  have hcard : (PiDvd q N W).card ≤ 4 := by
    calc (PiDvd q N W).card
        ≤ ({⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩} : Finset GaussianInt).card :=
          Finset.card_le_card hsub
      _ = 4 := by decide
  exact_mod_cast hcard

/-! ### The elementary real inequality for the large-`q` case -/

/-- **The bookkeeping inequality.**  If `q ≥ 2`, `2 ≤ N ≤ M`, `q ≤ 16N` and `0 ≤ x ≤ 64Mq`, then

  `1 + log(x+2)/log q ≤ (1/log 6 + (log 1024/log 6 + 1)/log 2) · log(MN+2)`.

Indeed `x + 2 ≤ 1024(MN+2) = 1024·(MN+2)`, so `log(x+2) ≤ log 1024 + log(MN+2)`, and
`log 1024 ≤ (log 1024/log 6) log(MN+2)`, `1 ≤ log(MN+2)/log 6` because `MN + 2 ≥ 6`. -/
lemma piDvd_log_arith_aux {q M N x : ℝ} (hq : 2 ≤ q) (hN : 2 ≤ N) (hNM : N ≤ M)
    (hqN : q ≤ 16 * N) (hx0 : 0 ≤ x) (hx : x ≤ 64 * M * q) :
    1 + Real.log (x + 2) / Real.log q ≤
      (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2) * Real.log (M * N + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog1024 : 0 < Real.log 1024 := Real.log_pos (by norm_num)
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogq2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hM2 : (2 : ℝ) ≤ M := le_trans hN hNM
  have hL6 : Real.log 6 ≤ Real.log (M * N + 2) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have hL0 : 0 < Real.log (M * N + 2) := lt_of_lt_of_le hlog6 hL6
  have hx3 : x + 2 ≤ 1024 * (M * N + 2) := by
    have h1 : 64 * M * q ≤ 64 * M * (16 * N) :=
      mul_le_mul_of_nonneg_left hqN (by linarith : (0 : ℝ) ≤ 64 * M)
    nlinarith [hx, h1]
  have hlogx : Real.log (x + 2) ≤ Real.log 1024 + Real.log (M * N + 2) := by
    have h1 : Real.log (x + 2) ≤ Real.log (1024 * (M * N + 2)) :=
      Real.log_le_log (by linarith) hx3
    rwa [Real.log_mul (by norm_num) (by linarith)] at h1
  have hlog1024' : Real.log 1024 ≤ (Real.log 1024 / Real.log 6) * Real.log (M * N + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog6]
    exact mul_le_mul_of_nonneg_left hL6 (le_of_lt hlog1024)
  have hkey : Real.log (x + 2) ≤ (Real.log 1024 / Real.log 6 + 1) * Real.log (M * N + 2) := by
    nlinarith [hlogx, hlog1024']
  have h1 : Real.log (x + 2) / Real.log q ≤
      ((Real.log 1024 / Real.log 6 + 1) / Real.log 2) * Real.log (M * N + 2) := by
    have hA : Real.log (x + 2) / Real.log q ≤ Real.log (x + 2) / Real.log 2 :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hlog2 hlogq2
    have hB : Real.log (x + 2) / Real.log 2 ≤
        ((Real.log 1024 / Real.log 6 + 1) * Real.log (M * N + 2)) / Real.log 2 :=
      div_le_div_of_nonneg_right hkey (le_of_lt hlog2)
    have hC : ((Real.log 1024 / Real.log 6 + 1) * Real.log (M * N + 2)) / Real.log 2 =
        ((Real.log 1024 / Real.log 6 + 1) / Real.log 2) * Real.log (M * N + 2) := by ring
    linarith [hA, hB, hC]
  have h2 : (1 : ℝ) ≤ (1 / Real.log 6) * Real.log (M * N + 2) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog6]
    linarith [hL6]
  have h3 : (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
        * Real.log (M * N + 2)
      = (1 / Real.log 6) * Real.log (M * N + 2)
        + ((Real.log 1024 / Real.log 6 + 1) / Real.log 2) * Real.log (M * N + 2) := by ring
  linarith [h1, h2, h3]

/-! ### The dyadic-range count -/

/-- **The number of Gaussian primes of a dyadic range dividing a fixed `W` is `≪ log(MN)`.**

`PiDvd q N W` is the finset of Gaussian primes `π` with `q < |π|² ≤ 2q` inside `gBox (KZ N)` that
divide `W`.  Route: for `q ≥ 2` apply `Work.FIArea1.gauss_prime_dvd_card_le`
(`♯S ≤ 4(1 + log|W|²/log q)`) together with `log q ≥ log 2` and `|W|² ≤ 64Mq ≤ 1024MN`, so that
`log(|W|²+2) ≤ C log(MN+2)`; for `1 ≤ q < 2` every `π ∈ S` has `2 ≤ |π|² ≤ 2q < 4`, and `3` is not
a sum of two squares, so `|π|² = 2` and `π ∈ {±1±i}`, whence `♯S ≤ 4 ≤ 4 log(MN+2)` (as
`MN ≥ 4`). -/
theorem pi_dvd_card_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M N : ℝ) (W : GaussianInt),
      1 ≤ q → 2 ≤ N → N ≤ M → q ≤ 16 * N → W ≠ 0 →
      (Work.FIPlan.gnorm W : ℝ) ≤ 64 * M * q →
      (((Work.FIArea1.PiDvd q N W).card : ℝ)) ≤ C * Real.log (M * N + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := gauss_prime_dvd_card_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog1024 : 0 < Real.log 1024 := Real.log_pos (by norm_num)
  have hbpos : 0 < 1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2 := by
    have h1 : 0 < 1 / Real.log 6 := div_pos one_pos hlog6
    have h2 : 0 < Real.log 1024 / Real.log 6 := div_pos hlog1024 hlog6
    have h3 : 0 < (Real.log 1024 / Real.log 6 + 1) / Real.log 2 := div_pos (by linarith) hlog2
    linarith
  have hCpos : 0 < C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
      + 4 / Real.log 6 := by
    have h1 := mul_pos hC0pos hbpos
    have h2 : 0 < 4 / Real.log 6 := div_pos (by norm_num) hlog6
    linarith
  refine ⟨C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
    + 4 / Real.log 6, hCpos, ?_⟩
  intro q M N W hq hN hNM hqN hW hWn
  have hL6 : Real.log 6 ≤ Real.log (M * N + 2) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have hL0 : 0 < Real.log (M * N + 2) := lt_of_lt_of_le hlog6 hL6
  by_cases hq2 : 2 ≤ q
  · -- large `q`: the fiber bound of a fixed `W` plus the log bookkeeping
    have hmem : ∀ π ∈ PiDvd q N W, Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ) ∧ π ∣ W := by
      intro π hπ
      rw [PiDvd, Finset.mem_filter] at hπ
      exact ⟨hπ.2.1, hπ.2.2.1, hπ.2.2.2.2⟩
    have hcard := hC0 W q (PiDvd q N W) hW (by linarith) hmem
    have harith := piDvd_log_arith_aux (x := (Work.FIPlan.gnorm W : ℝ))
      hq2 hN hNM hqN (by positivity) hWn
    have h1 : ((PiDvd q N W).card : ℝ)
        ≤ C0 * ((1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
            * Real.log (M * N + 2)) :=
      le_trans hcard (mul_le_mul_of_nonneg_left harith (le_of_lt hC0pos))
    have h2 : C0 * ((1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
          * Real.log (M * N + 2))
        ≤ (C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
            + 4 / Real.log 6) * Real.log (M * N + 2) := by
      have hle : C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
          ≤ C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
            + 4 / Real.log 6 := le_add_of_nonneg_right (by positivity)
      calc C0 * ((1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
              * Real.log (M * N + 2))
          = (C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2))
              * Real.log (M * N + 2) := by ring
        _ ≤ (C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
              + 4 / Real.log 6) * Real.log (M * N + 2) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hL0)
    linarith
  · -- small `q`: at most the four primes of norm `2`
    have hql : q < 2 := not_le.mp hq2
    have hcard := piDvd_card_le_four_of_lt_two (q := q) (N := N) (W := W) hq hql
    have h4 : (4 : ℝ) ≤ (4 / Real.log 6) * Real.log (M * N + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog6]
      linarith
    have hle : (4 : ℝ) / Real.log 6
        ≤ C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
          + 4 / Real.log 6 := by
      have h0 : 0 ≤ C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2) :=
        le_of_lt (mul_pos hC0pos hbpos)
      linarith
    calc ((PiDvd q N W).card : ℝ) ≤ 4 := hcard
      _ ≤ (4 / Real.log 6) * Real.log (M * N + 2) := h4
      _ ≤ (C0 * (1 / Real.log 6 + (Real.log 1024 / Real.log 6 + 1) / Real.log 2)
            + 4 / Real.log 6) * Real.log (M * N + 2) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hL0)

end

end Work.FIArea1
