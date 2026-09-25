import Mathlib
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Commons.Analysis.SpecialFunctions.Log.convex_combo_log_le
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

/-!
# Region II: `logl n ≤ log n` for `173 ≤ n ≤ 501`

`logl` is the piecewise-linear chord lower bound for `Real.log`:

* on `[173, 273]` it is the chord through `(173, lg173)` and `(273, lg273)`;
* on `[274, 514]` it is the chord through `(274, lg273)` and `(514, lg513)`.

The three `lg…` values are the certified `ltOf` lower brackets for `10^9 log` at
`173`, `273` and `513` (`lg173 = ltOf 173 / 10^9`, etc.).  Since `log` is concave,
its graph lies above every chord, and since the `lg…` values are *lower* bounds for
`log` at the relevant endpoints, the chord through them lies below `log` too.
-/

set_option maxHeartbeats 0

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

/-- `lg173 = ltOf 173 / 10^9` is a lower bound for `log 173`. -/
theorem lg173_le_log : lg173 ≤ Real.log 173 := by
  have hlog := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 173 (by norm_num)
  have hlt : Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 173 = 5153259971 := by decide
  rw [hlt] at hlog
  have hlog' : (5153259971 : ℝ) ≤ 10 ^ 9 * Real.log 173 := by simpa using hlog
  unfold lg173
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
  linarith [hlog']

/-- `lg273 = ltOf 273 / 10^9` is a lower bound for `log 273`. -/
theorem lg273_le_log : lg273 ≤ Real.log 273 := by
  have hlog := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 273 (by norm_num)
  have hlt : Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 273 = 5609470336 := by decide
  rw [hlt] at hlog
  have hlog' : (5609470336 : ℝ) ≤ 10 ^ 9 * Real.log 273 := by simpa using hlog
  unfold lg273
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
  linarith [hlog']

/-- `lg513 = ltOf 513 / 10^9` is a lower bound for `log 513`. -/
theorem lg513_le_log : lg513 ≤ Real.log 513 := by
  have hlog := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 513 (by norm_num)
  have hlt : Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 513 = 6240274220 := by decide
  rw [hlt] at hlog
  have hlog' : (6240274220 : ℝ) ≤ 10 ^ 9 * Real.log 513 := by simpa using hlog
  unfold lg513
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
  linarith [hlog']

theorem logl_le_log (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    Work.RHContract.A.RegionII.logl n ≤ Real.log (n : ℝ) := by
  unfold Work.RHContract.A.RegionII.logl
  by_cases hn : n ≤ 273
  · rw [if_pos hn]
    have hn1 : (173 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have hn2 : (n : ℝ) ≤ 273 := by exact_mod_cast hn
    set t : ℝ := ((n : ℝ) - 173) / 100 with ht
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (by linarith) (by norm_num)
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by norm_num : (0 : ℝ) < 100)]; linarith
    have hconv :=
      Commons.Analysis.SpecialFunctions.Log.convex_combo_log_le 173 273 t
        (by norm_num) (by norm_num) ht0 ht1
    have harg : (1 - t) * 173 + t * 273 = (n : ℝ) := by
      rw [ht]; field_simp; ring
    rw [harg] at hconv
    have hchord : chordB n = (1 - t) * lg173 + t * lg273 := by
      rw [ht]; unfold chordB; field_simp; ring
    rw [hchord]
    have hw1 : 0 ≤ 1 - t := by linarith
    have hstep : (1 - t) * lg173 + t * lg273
        ≤ (1 - t) * Real.log 173 + t * Real.log 273 :=
      add_le_add (mul_le_mul_of_nonneg_left lg173_le_log hw1)
        (mul_le_mul_of_nonneg_left lg273_le_log ht0)
    linarith [hstep, hconv]
  · rw [if_neg hn]
    have hn274 : 274 ≤ n := by omega
    have hn1 : (274 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn274
    have hn2 : (n : ℝ) ≤ 501 := by exact_mod_cast h2
    set t : ℝ := ((n : ℝ) - 274) / 240 with ht
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (by linarith) (by norm_num)
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by norm_num : (0 : ℝ) < 240)]; linarith
    have hconv :=
      Commons.Analysis.SpecialFunctions.Log.convex_combo_log_le 274 514 t
        (by norm_num) (by norm_num) ht0 ht1
    have harg : (1 - t) * 274 + t * 514 = (n : ℝ) := by
      rw [ht]; field_simp; ring
    rw [harg] at hconv
    have hchord : chordA n = (1 - t) * lg273 + t * lg513 := by
      rw [ht]; unfold chordA; field_simp; ring
    rw [hchord]
    have hw1 : 0 ≤ 1 - t := by linarith
    have h273 : lg273 ≤ Real.log 274 :=
      le_trans lg273_le_log
        (Real.log_le_log (by norm_num : (0 : ℝ) < 273) (by norm_num : (273 : ℝ) ≤ 274))
    have h513 : lg513 ≤ Real.log 514 :=
      le_trans lg513_le_log
        (Real.log_le_log (by norm_num : (0 : ℝ) < 513) (by norm_num : (513 : ℝ) ≤ 514))
    have hstep : (1 - t) * lg273 + t * lg513
        ≤ (1 - t) * Real.log 274 + t * Real.log 514 :=
      add_le_add (mul_le_mul_of_nonneg_left h273 hw1)
        (mul_le_mul_of_nonneg_left h513 ht0)
    linarith [hstep, hconv]

end Work.RHContract.A.regionII
