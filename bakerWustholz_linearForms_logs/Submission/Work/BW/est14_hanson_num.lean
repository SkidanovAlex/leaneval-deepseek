import Mathlib
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.est14_regime2_step
import Submission.Work.BW.est14_regime2_base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Hanson numeric inequality `est14_hanson_num`

`K = #{i ≤ n : syl i ≤ n}` with `syl` Sylvester's sequence (`Submission.Work.BW.ulcm_le_three_pow`).
For `n ≥ 4096`, `K * log n + log n + log (n+1) + 1 + 1.0826 n ≤ n * log 3`.

Two regimes:

* `4096 ≤ n < 3263443`: `K ≤ 5` (only `syl 0,…,syl 4 = 2,3,7,43,1807` can be `≤ n`), so it
  suffices that `6 log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` (`est14_regime1`).
* `n ≥ 3263443`: `2 ^ i ≤ syl i` gives `K ≤ log n / log 2 + 1`, so it suffices that
  `(log n)^2 / log 2 + 2 log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` (`est14_regime2`, whose
  forward difference is `≤ 1.0986 ≤ log 3`, with base case at `n = 3263443`).

The small helpers are re-proved here (privately) so the file depends only on the stable `syl`
API, not on the inlined copies living in `ulcm_le_three_pow` or the standalone
`syl_card_le_*`/`num_regime1` modules.
-/

namespace Work.BW

open Finset

/-! ## Elementary helpers (private copies) -/

private lemma est14_log_le_log4096_add {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ Real.log 4096 + (x - 4096) / 4096 := by
  have h4096 : (4096 : ℝ) ≠ 0 := by norm_num
  have h := Real.log_le_sub_one_of_pos (x := x / 4096) (by positivity)
  rw [Real.log_div (ne_of_gt hx) h4096] at h
  have hx' : x / 4096 - 1 = (x - 4096) / 4096 := by ring
  linarith [h, hx']

/-- In the first regime only `syl 0 ≤ … ≤ syl 4 = 1807` can be `≤ n`. -/
private theorem est14_K_le_five (n : ℕ) (hn : n < 3263443) :
    ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card ≤ 5 := by
  have hsyl5 : syl 5 = 3263443 := by decide
  calc ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card
      ≤ (Finset.range 5).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_range]
        by_contra hcon
        have h5i : 5 ≤ i := by omega
        have hle : syl 5 ≤ syl i := syl_mono h5i
        omega
    _ = 5 := Finset.card_range 5

private lemma est14_syl_two_pow_le (i : ℕ) : 2 ^ i ≤ syl i := by
  have hprod : (∏ j ∈ Finset.range i, syl j) = syl i - 1 := syl_prod i
  have h2 : 2 ^ i ≤ ∏ j ∈ Finset.range i, syl j := by
    calc 2 ^ i = ∏ _j ∈ Finset.range i, (2 : ℕ) := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range i, syl j := Finset.prod_le_prod (fun j _ => syl_two_le j)
  omega

/-- `K ≤ log n / log 2 + 1`, because `syl i ≥ 2 ^ i`. -/
private theorem est14_K_le_log (n : ℕ) :
    (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) ≤
      Real.log n / Real.log 2 + 1 := by
  set S := (Finset.range (n + 1)).filter (fun i => syl i ≤ n) with hS
  set m := Nat.floor (Real.log n / Real.log 2) with hm
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : S ⊆ Finset.range (m + 1) := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    obtain ⟨hirange, hsyl⟩ := hi
    rw [Finset.mem_range] at hirange ⊢
    have h2i : 2 ^ i ≤ syl i := est14_syl_two_pow_le i
    have hle : (2 : ℝ) ^ i ≤ (n : ℝ) := by
      have : ((2 ^ i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans h2i hsyl
      simpa using this
    have hlog : ((i : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ i) hle
      rwa [Real.log_pow] at h
    have hile : ((i : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      linarith
    have : i ≤ m := by
      rw [hm]
      exact Nat.le_floor hile
    omega
  have hcard_nat : S.card ≤ m + 1 := by
    simpa using Finset.card_le_card hsub
  have hcard : (S.card : ℝ) ≤ (m : ℝ) + 1 := by
    have h : ((S.card : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard_nat
    push_cast at h
    linarith
  have hmle : (m : ℝ) ≤ Real.log n / Real.log 2 := by
    apply Nat.floor_le
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [Real.log_zero]
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (le_of_lt hlog2pos)
  linarith

/-- First-regime inequality `6 log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` for `n ≥ 4096`,
by the tangent bound `log x ≤ log 4096 + (x - 4096)/4096`. -/
private theorem est14_regime1 (n : ℕ) (hn : 4096 ≤ n) :
    6 * Real.log n + Real.log (n + 1) + 1 + 1.0826 * n ≤ n * Real.log 3 := by
  have hnR : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1 : Real.log n ≤ Real.log 4096 + ((n : ℝ) - 4096) / 4096 :=
    est14_log_le_log4096_add hnpos
  have h2 : Real.log (n + 1) ≤ Real.log 4096 + ((n : ℝ) + 1 - 4096) / 4096 := by
    have h := est14_log_le_log4096_add (x := (n : ℝ) + 1) hn1pos
    simpa using h
  have hlog4096 : Real.log 4096 = 12 * Real.log 2 := by
    have h : (4096 : ℝ) = 2 ^ 12 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have h4 : Real.log 4096 ≤ 8.3184 := by
    rw [hlog4096]
    have hlt := Real.log_two_lt_d9
    nlinarith
  have h5 : (1.0986122885 : ℝ) ≤ Real.log 3 := le_of_lt Real.log_three_gt_d9
  have hmain : 6 * Real.log n + Real.log (n + 1) + 1 + 1.0826 * n
      ≤ (n : ℝ) * 1.0986122885 := by
    linarith [h1, h2, h4, hnR]
  have hmult : (n : ℝ) * 1.0986122885 ≤ (n : ℝ) * Real.log 3 :=
    mul_le_mul_of_nonneg_left h5 (le_of_lt hnpos)
  linarith [hmain, hmult]

/-! ## Second regime -/

/-- Regime-2 numerical inequality, obtained by induction on `n` from the base case
`est14_regime2_base` at `n = 3263443` and the increment estimate `est14_regime2_step`
(the forward difference of the left-hand side is at most `0.016 + 1.0826 = 1.0986 ≤ log 3`). -/
theorem est14_regime2 (n : ℕ) (hn : 3263443 ≤ n) :
    (Real.log (n : ℝ)) ^ 2 / Real.log 2 + 2 * Real.log (n : ℝ) + Real.log ((n : ℝ) + 1)
      + 1 + 1.0826 * (n : ℝ) ≤ (n : ℝ) * Real.log 3 := by
  have hlog3 : (1.0986 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  refine Nat.le_induction ?base ?step n hn
  · -- base case at `n = 3263443`
    rw [show ((3263443 : ℕ) : ℝ) + 1 = (3263444 : ℝ) by norm_num]
    exact est14_regime2_base
  · -- inductive step: control the forward difference
    intro n hn ih
    push_cast
    have harg : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    simp only [harg]
    have hS := est14_regime2_step n hn
    have h1 : (Real.log ((n : ℝ) + 1)) ^ 2 / Real.log 2 + 2 * Real.log ((n : ℝ) + 1)
          + Real.log ((n : ℝ) + 2) + 1 + 1.0826 * ((n : ℝ) + 1)
        = ((Real.log (n : ℝ)) ^ 2 / Real.log 2 + 2 * Real.log (n : ℝ) + Real.log ((n : ℝ) + 1)
            + 1 + 1.0826 * (n : ℝ))
          + (((Real.log ((n : ℝ) + 1)) ^ 2 - (Real.log (n : ℝ)) ^ 2) / Real.log 2
              + 2 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
              + (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) + 1.0826) := by ring
    rw [show ((n : ℝ) + 1) * Real.log 3 = (n : ℝ) * Real.log 3 + Real.log 3 by ring]
    linarith [h1, hS, ih, hlog3]

/-! ## The target -/

/-- **Numeric inequality for Hanson's bound.** For `n ≥ 4096`,
`K * log n + log n + log (n+1) + 1 + 1.0826 n ≤ n * log 3`, where `K = #{i ≤ n : syl i ≤ n}`
is the number of Sylvester terms `syl i ≤ n` (`syl` is Sylvester's sequence, defined in
`Submission.Work.BW.ulcm_le_three_pow`). -/
theorem est14_hanson_num (n : ℕ) (hn : 4096 ≤ n) :
    (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) * Real.log n
      + Real.log n + Real.log (n + 1) + 1 + n * 1.0826 ≤ n * Real.log 3 := by
  set K : ℕ := ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card with hK
  have hn1 : 1 ≤ n := by omega
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  rcases lt_or_ge n 3263443 with hlt | hge
  · -- Regime 1: at most five Sylvester terms are `≤ n`.
    have hK5 : K ≤ 5 := est14_K_le_five n hlt
    have hK5r : (K : ℝ) ≤ 5 := by exact_mod_cast hK5
    have hmul : (K : ℝ) * Real.log n ≤ 5 * Real.log n :=
      mul_le_mul_of_nonneg_right hK5r hlogpos
    have hr := est14_regime1 n hn
    linarith [hmul, hr]
  · -- Regime 2: `K ≤ log₂ n + 1`.
    have hKl : (K : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
      rw [hK]; exact est14_K_le_log n
    have hmul : (K : ℝ) * Real.log n ≤ (Real.log n / Real.log 2 + 1) * Real.log n :=
      mul_le_mul_of_nonneg_right hKl hlogpos
    have hr := est14_regime2 n hge
    have hid : (Real.log n / Real.log 2 + 1) * Real.log n
        = (Real.log n) ^ 2 / Real.log 2 + Real.log n := by ring
    linarith [hmul, hr, hid.le, hid.ge]

end Work.BW
