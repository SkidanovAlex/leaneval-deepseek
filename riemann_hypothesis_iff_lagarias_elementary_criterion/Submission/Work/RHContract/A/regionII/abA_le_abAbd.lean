import Mathlib
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Work.RHContract.A.regionII.logl_le_log
import Submission.Work.RHContract.A.regionII.log_le_logU
import Submission.Work.RHContract.A.regionII.sqL_le_sqrt

/-!
# Region II, part A: `abA n ≤ abAbd n` for `173 ≤ n ≤ 501`

`abA n` is the exact loss coming from the Abel-identity range `(n, 501]`; `abAbd n` is the
explicit rational bound for it used in the final numeric check.  Both are sums of the same
five summands, and `abAbd` is what one gets from `abA` by replacing every transcendental
quantity by its certified bracketing, always in the direction that *increases* the summand:

* `Real.sqrt n ↦ sqL n ≤ √n` and `Real.log n ↦ logl n ≤ log n` in the denominators,
  together with `sq501u ≥ √501` in the first summand;
* `u n = 1/(n log n) ↦ 1/(n · logU n)` with `logU n ≥ log n`, while `u 501` is replaced by
  its lower bracket `u501l ≤ u 501` in the third summand and by its upper bracket
  `u501u ≥ u 501` in the second;
* `χ n = (2 + 1/log n)/log n ↦ chiU n ≥ χ n`.

So the proof is a summand-by-summand comparison; each comparison is the elementary
monotonicity of `1/x`, `x ↦ a/x` and multiplication by nonnegative factors.
-/

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII
open Commons.NumberTheory.Chebyshev.ThetaBracket

noncomputable section

/-! ## Certified rational brackets for `log` -/

lemma ltOf_173 : ltOf 173 = 5153259971 := by decide
lemma ltOf_273 : ltOf 273 = 5609470336 := by decide
lemma ltOf_513 : ltOf 513 = 6240274220 := by decide
lemma ltOf_501 : ltOf 501 = 6215068509 := by decide
lemma utOf_274 : utOf 274 = 5613282966 := by decide
lemma utOf_512 : utOf 512 = 6238440000 := by decide
lemma ten9 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num

lemma lg173_le_log173 : lg173 ≤ Real.log 173 := by
  have h := ltOf_le_log 173 (by norm_num)
  rw [ltOf_173, ten9] at h
  have h' : (5153259971 : ℝ) ≤ 1000000000 * Real.log (173 : ℝ) := by simpa using h
  unfold lg173
  rw [ten9, div_le_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

lemma lg273_le_log273 : lg273 ≤ Real.log 273 := by
  have h := ltOf_le_log 273 (by norm_num)
  rw [ltOf_273, ten9] at h
  have h' : (5609470336 : ℝ) ≤ 1000000000 * Real.log (273 : ℝ) := by simpa using h
  unfold lg273
  rw [ten9, div_le_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

lemma lg513_le_log513 : lg513 ≤ Real.log 513 := by
  have h := ltOf_le_log 513 (by norm_num)
  rw [ltOf_513, ten9] at h
  have h' : (6240274220 : ℝ) ≤ 1000000000 * Real.log (513 : ℝ) := by simpa using h
  unfold lg513
  rw [ten9, div_le_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

lemma lg501l_le_log501 : lg501l ≤ Real.log 501 := by
  have h := ltOf_le_log 501 (by norm_num)
  rw [ltOf_501, ten9] at h
  have h' : (6215068509 : ℝ) ≤ 1000000000 * Real.log (501 : ℝ) := by simpa using h
  unfold lg501l
  rw [ten9, div_le_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

lemma log274_le_lg274u : Real.log 274 ≤ lg274u := by
  have h := log_le_utOf 274 (by norm_num)
  rw [utOf_274, ten9] at h
  have h' : 1000000000 * Real.log (274 : ℝ) ≤ (5613282966 : ℝ) := by simpa using h
  unfold lg274u
  rw [ten9, le_div_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

lemma log512_le_lg512u : Real.log 512 ≤ lg512u := by
  have h := log_le_utOf 512 (by norm_num)
  rw [utOf_512, ten9] at h
  have h' : 1000000000 * Real.log (512 : ℝ) ≤ (6238440000 : ℝ) := by simpa using h
  unfold lg512u
  rw [ten9, le_div_iff₀ (by norm_num : (0:ℝ) < 1000000000)]
  linarith

/-- `√501 ≤ 2238310/10^5`. -/
lemma sqrt501_le_sq501u : Real.sqrt 501 ≤ sq501u := by
  have h : (501 : ℝ) ≤ sq501u ^ 2 := by norm_num [sq501u]
  have h0 : (0 : ℝ) ≤ sq501u := by norm_num [sq501u]
  calc Real.sqrt 501 ≤ Real.sqrt (sq501u ^ 2) := Real.sqrt_le_sqrt h
    _ = sq501u := Real.sqrt_sq h0

/-! ## Positivity and monotonicity of the auxiliary quantities -/

/-- `0 < logl n`. -/
lemma logl_pos (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) : 0 < logl n := by
  have hg : 0 < lg173 := by norm_num [lg173]
  have hg' : lg173 ≤ lg273 := by norm_num [lg173, lg273]
  have hh : 0 < lg273 := by norm_num [lg273]
  have hh' : lg273 ≤ lg513 := by norm_num [lg273, lg513]
  unfold logl chordB chordA
  split_ifs with h
  · have hn : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h3 : 0 ≤ ((n:ℝ) - 173) * (lg273 - lg173) / 100 :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    linarith
  · have hn274 : 274 ≤ n := by omega
    have hn : (274:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn274
    have h3 : 0 ≤ ((n:ℝ) - 274) * (lg513 - lg273) / 240 :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    linarith

/-- `0 < sqL n`. -/
lemma sqL_pos (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) : 0 < sqL n := by
  have hg : 0 < sq173l := by norm_num [sq173l]
  have hg' : sq173l ≤ sq273l := by norm_num [sq173l, sq273l]
  have hh : 0 < sq274l := by norm_num [sq274l]
  have hh' : sq274l ≤ sq501l := by norm_num [sq274l, sq501l]
  unfold sqL
  split_ifs with h
  · have hn : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h3 : 0 ≤ ((n:ℝ) - 173) * (sq273l - sq173l) / 100 :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    linarith
  · have hn274 : 274 ≤ n := by omega
    have hn : (274:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn274
    have h3 : 0 ≤ ((n:ℝ) - 274) * (sq501l - sq274l) / 227 :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    linarith

/-- `t ↦ (2 + 1/t)/t` is antitone on `(0,∞)`. -/
lemma two_add_inv_div_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (2 + 1/t)/t ≤ (2 + 1/s)/s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hst' : 0 ≤ t - s := by linarith
  have hpos : 0 ≤ 2*s*t + s + t := by positivity
  have hkey : 0 ≤ (t - s) * (2*s*t + s + t) := mul_nonneg hst' hpos
  have h2 : (2 + 1/s)/s - (2 + 1/t)/t
      = ((t - s) * (2*s*t + s + t)) / (s*t)^2 := by
    field_simp
    ring
  have h3 : 0 ≤ (2 + 1/s)/s - (2 + 1/t)/t := by
    rw [h2]
    exact div_nonneg hkey (by positivity)
  linarith

/-- `χ n ≤ chiU n`. -/
lemma chAb_le_chiU (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    chAb (n : ℝ) ≤ chiU n := by
  have hlp : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  unfold chAb chiU
  exact two_add_inv_div_antitone (logl_pos n h1 h2) (logl_le_log n h1 h2)

/-- `u501l ≤ u 501`. -/
lemma u501l_le_u501 : u501l ≤ 1 / (501 * Real.log 501) := by
  have h501 : Real.log 501 ≤ lg512u :=
    le_trans (Real.log_le_log (by norm_num) (by norm_num : (501:ℝ) ≤ 512)) log512_le_lg512u
  unfold u501l
  apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < 501 * Real.log 501)
  nlinarith [h501]

/-- `u 501 ≤ u501u`. -/
lemma log501u_le_u501u : 1 / (501 * Real.log 501) ≤ u501u := by
  have h501 : lg501l ≤ Real.log 501 := lg501l_le_log501
  unfold u501u
  apply one_div_le_one_div_of_le (by norm_num [lg501l] : (0:ℝ) < 501 * lg501l)
  nlinarith [h501]

theorem abA_le_abAbd (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    Work.RHContract.A.RegionII.abA n ≤ Work.RHContract.A.RegionII.abAbd n := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn501 : (n : ℝ) ≤ 501 := by exact_mod_cast h2
  have hlogl_le : logl n ≤ Real.log (n : ℝ) := logl_le_log n h1 h2
  have hlogl_pos : 0 < logl n := logl_pos n h1 h2
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := hlogn_pos.le
  have hlog_le_U : Real.log (n : ℝ) ≤ logU n := log_le_logU n h1 h2
  have hsqL_le : sqL n ≤ Real.sqrt (n : ℝ) := sqL_le_sqrt n h1 h2
  have hsqL_pos : 0 < sqL n := sqL_pos n h1 h2
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsq_nn : 0 ≤ Real.sqrt (n : ℝ) := hsq_pos.le
  have hchi : chAb (n : ℝ) ≤ chiU n := chAb_le_chiU n h1 h2
  have hchiU_pos : 0 < chiU n := by
    unfold chiU
    apply div_pos _ hlogl_pos
    have := one_div_pos.mpr hlogl_pos
    linarith
  have hchiU_nn : 0 ≤ chiU n := hchiU_pos.le
  have hsqrt501_le : Real.sqrt 501 ≤ sq501u := sqrt501_le_sq501u
  have hsqrt501_pos : 0 < Real.sqrt 501 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt501_nn : 0 ≤ Real.sqrt 501 := hsqrt501_pos.le
  have hlg501_pos : 0 < Real.log 501 := Real.log_pos (by norm_num)
  have hlogn_le501 : Real.log (n : ℝ) ≤ Real.log 501 := Real.log_le_log hnpos hn501
  have hsqn_le501 : Real.sqrt (n : ℝ) ≤ Real.sqrt 501 := Real.sqrt_le_sqrt hn501
  -- the three "product" comparisons used over and over
  have hNlogn_le : (n : ℝ) * Real.log (n : ℝ) ≤ 501 * Real.log 501 :=
    mul_le_mul hn501 hlogn_le501 hlogn_nn (by norm_num)
  have hNlogl_le : (n : ℝ) * logl n ≤ 501 * lg512u := by
    have h1' : logl n ≤ lg512u :=
      le_trans hlogl_le (le_trans hlogn_le501
        (le_trans (Real.log_le_log (by norm_num) (by norm_num : (501:ℝ) ≤ 512)) log512_le_lg512u))
    exact mul_le_mul hn501 h1' hlogl_pos.le (by norm_num)
  have hNsqrt_le : (n : ℝ) * Real.sqrt (n : ℝ) ≤ 501 * Real.sqrt 501 :=
    mul_le_mul hn501 hsqn_le501 hsq_nn (by norm_num)
  -- (1) first summand
  have K1 : (1 - (64 / 100) / Real.sqrt (n : ℝ)) / ((n : ℝ) * Real.log (n : ℝ))
      ≤ (1 - (64 / 100) / sq501u) / ((n : ℝ) * logl n) := by
    apply div_le_div₀
    · have h : (64 / 100) / sq501u ≤ 1 := by
        rw [div_le_one (by norm_num [sq501u] : (0:ℝ) < sq501u)]
        norm_num [sq501u]
      linarith
    · have h : (64 / 100) / sq501u ≤ (64 / 100) / Real.sqrt (n : ℝ) := by
        have hsq : Real.sqrt (n : ℝ) ≤ sq501u := le_trans hsqn_le501 hsqrt501_le
        exact div_le_div_of_nonneg_left (by norm_num) hsq_pos hsq
      linarith
    · exact mul_pos hnpos hlogl_pos
    · exact mul_le_mul_of_nonneg_left hlogl_le hnpos.le
  -- (2) the `-2 * (u n - u 501)` summand
  have K2 : -2 * (1 / ((n : ℝ) * Real.log (n : ℝ)) - 1 / (501 * Real.log 501))
      ≤ -(2 / ((n : ℝ) * logU n)) + 2 * u501u := by
    have hA : 1 / ((n : ℝ) * logU n) ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
      apply one_div_le_one_div_of_le (mul_pos hnpos hlogn_pos)
      exact mul_le_mul_of_nonneg_left hlog_le_U hnpos.le
    have hB : 1 / (501 * Real.log 501) ≤ u501u := log501u_le_u501u
    have hA2 : 2 * (1 / ((n : ℝ) * logU n)) ≤ 2 * (1 / ((n : ℝ) * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    have hB2 : 2 * (1 / (501 * Real.log 501)) ≤ 2 * u501u :=
      mul_le_mul_of_nonneg_left hB (by norm_num)
    have e1 : 2 / ((n : ℝ) * logU n) = 2 * (1 / ((n : ℝ) * logU n)) := by ring
    rw [e1]
    linarith
  -- (3) the `(u n - u 501)/(log n + 1)` summand
  have K3 : (1 / ((n : ℝ) * Real.log (n : ℝ)) - 1 / (501 * Real.log 501))
        / (Real.log (n : ℝ) + 1)
      ≤ (1 / ((n : ℝ) * logl n) - u501l) / (logl n + 1) := by
    apply div_le_div₀
    · have h : u501l ≤ 1 / ((n : ℝ) * logl n) := by
        rw [u501l]
        apply one_div_le_one_div_of_le (mul_pos hnpos hlogl_pos)
        exact hNlogl_le
      linarith
    · have h1' : 1 / ((n : ℝ) * Real.log (n : ℝ)) ≤ 1 / ((n : ℝ) * logl n) := by
        apply one_div_le_one_div_of_le (mul_pos hnpos hlogl_pos)
        exact mul_le_mul_of_nonneg_left hlogl_le hnpos.le
      have h2' : u501l ≤ 1 / (501 * Real.log 501) := u501l_le_u501
      linarith
    · linarith
    · linarith
  -- (4) the `χ n / 2 * (n⁻² - 501⁻²)` summand
  have hX_nn : 0 ≤ (1 / (n : ℝ) ^ 2 - 1 / 501 ^ 2 : ℝ) := by
    have h : 1 / (501:ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ) ^ 2)
      nlinarith
    linarith
  have K4 : chAb (n : ℝ) / 2 * (1 / (n : ℝ) ^ 2 - 1 / 501 ^ 2)
      ≤ chiU n / 2 * (1 / (n : ℝ) ^ 2 - 1 / 501 ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hX_nn
    linarith
  -- (5) the `(189/100) χ n (2/3) (n^{-3/2} - 501^{-3/2})` summand
  have hY_nn : 0 ≤ (1 / ((n : ℝ) * Real.sqrt (n : ℝ)) - 1 / (501 * Real.sqrt 501) : ℝ) := by
    have h : 1 / (501 * Real.sqrt 501) ≤ 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      apply one_div_le_one_div_of_le (mul_pos hnpos hsq_pos)
      exact hNsqrt_le
    linarith
  have hY : 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) - 1 / (501 * Real.sqrt 501)
      ≤ 1 / ((n : ℝ) * sqL n) - inv501_32_lb := by
    have h1' : 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 1 / ((n : ℝ) * sqL n) := by
      apply one_div_le_one_div_of_le (mul_pos hnpos hsqL_pos)
      exact mul_le_mul_of_nonneg_left hsqL_le hnpos.le
    have h2' : inv501_32_lb ≤ 1 / (501 * Real.sqrt 501) := by
      rw [inv501_32_lb]
      apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < 501 * Real.sqrt 501)
      exact mul_le_mul_of_nonneg_left hsqrt501_le (by norm_num)
    linarith
  have K5 : (189 / 100) * chAb (n : ℝ) * (2 / 3)
        * (1 / ((n : ℝ) * Real.sqrt (n : ℝ)) - 1 / (501 * Real.sqrt 501))
      ≤ (189 / 100) * chiU n * (2 / 3)
        * (1 / ((n : ℝ) * sqL n) - inv501_32_lb) := by
    have hb : 0 ≤ (189 / 100) * chiU n * (2 / 3) := by positivity
    have ha : (189 / 100) * chAb (n : ℝ) * (2 / 3) ≤ (189 / 100) * chiU n * (2 / 3) := by
      linarith
    exact mul_le_mul ha hY hY_nn hb
  unfold abA abAbd
  simp only [uAb]
  linarith [K1, K2, K3, K4, K5]

end

end Work.RHContract.A.regionII
