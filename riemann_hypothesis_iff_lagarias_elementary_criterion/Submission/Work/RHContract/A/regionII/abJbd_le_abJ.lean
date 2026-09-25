import Mathlib
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

/-!
# Region II: `abJbd ≤ abJ z` for `30000 ≤ z ≤ 10^5`

`abJ z` is the part of the Abel lower bound for `Σ_{501<p≤z} 1/p²` coming from the range
`(501, z]`; `abJbd` is the explicit rational lower bound for `abJ` on `[30000, 10^5]`.
Both are the sum of four terms, and each term of `abJ z` is bounded below by the
corresponding term of `abJbd` separately:

* `(96/100)/(z log z) ≥ (96/100)/(10^5 · log 10^5) ≥ (96/100)/(10^5 · lg100ku)`;
* `2(u(501) − u(z)) ≥ 2(u501l − uzu)`, using `u501l ≤ u(501)` and `u(30000) ≤ u(z) ≤ uzu`;
* `−(u(501) − u(z))/(log 501 + 1) ≥ −(u501u − uzl)/(lg501l + 1)`;
* `−(23/10)·χ(501)·(2/3)·(501^{-3/2} − z^{-3/2}) ≥ −(23/10)·chi501u·(2/3)·inv501_32_ub`.

The numerical inputs are the certified `10^9·log` brackets `ltOf`/`utOf` of
`theta_bracket_finite_range` (the constants of `abnum` are exactly the corresponding
table values) together with elementary monotonicity of `t ↦ 1/(t log t)` and
`t ↦ (2 + 1/t)/t`.
-/

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

set_option maxHeartbeats 1000000

/-! ### Certifed logarithms -/

/-- `lg501l = 6215068509/10^9 ≤ log 501`. -/
lemma log501_lb : lg501l ≤ Real.log 501 := by
  have hnat : Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 501 = 6215068509 := by decide
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 501 (by norm_num)
  have h1 : lg501l = (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 501 : ℝ) / 10^9 := by
    rw [lg501l, hnat]; norm_num
  rw [h1, div_le_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  calc (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 501 : ℝ)
        ≤ 10^9 * Real.log 501 := h
    _ = Real.log 501 * 10^9 := by ring

/-- `log 512 ≤ lg512u = 6238440000/10^9`. -/
lemma log512_ub : Real.log 512 ≤ lg512u := by
  have hnat : Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 512 = 6238440000 := by decide
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.log_le_utOf 512 (by norm_num)
  have h1 : lg512u = (Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 512 : ℝ) / 10^9 := by
    rw [lg512u, hnat]; norm_num
  rw [h1, le_div_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  calc Real.log 512 * 10^9 = 10^9 * Real.log 512 := by ring
    _ ≤ (Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 512 : ℝ) := h

/-- `log (10^5) ≤ lg100ku = 11525819454/10^9`. -/
lemma log100k_ub : Real.log (10^5) ≤ lg100ku := by
  have hnat : Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 100000 = 11525819454 := by decide
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.log_le_utOf 100000 (by norm_num)
  have h1 : lg100ku = (Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 100000 : ℝ) / 10^9 := by
    rw [lg100ku, hnat]; norm_num
  have h2 : Real.log ((10:ℝ)^5) = Real.log 100000 := by norm_num
  rw [h1, h2, le_div_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  calc Real.log 100000 * 10^9 = 10^9 * Real.log 100000 := by ring
    _ ≤ (Commons.NumberTheory.Chebyshev.ThetaBracket.utOf 100000 : ℝ) := h

/-- `lg30000l = 10308020696/10^9 ≤ log 30000`. -/
lemma log30000_lb : lg30000l ≤ Real.log 30000 := by
  have hnat : Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 30000 = 10308020696 := by decide
  have h := Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf_le_log 30000 (by norm_num)
  have h1 : lg30000l = (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 30000 : ℝ) / 10^9 := by
    rw [lg30000l, hnat]; norm_num
  rw [h1, div_le_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  calc (Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf 30000 : ℝ)
        ≤ 10^9 * Real.log 30000 := h
    _ = Real.log 30000 * 10^9 := by ring

/-- `sq501l = 22383/1000 ≤ √501`. -/
lemma sq501_lb : sq501l ≤ Real.sqrt 501 := by
  rw [sq501l]
  rw [Real.le_sqrt' (by norm_num : (0:ℝ) < 22383/10^3)]
  norm_num

/-! ### Elementary monotonicity -/

/-- `t ↦ (2 + 1/t)/t` is antitone on the positive reals. -/
lemma chi_anti {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    (2 + 1/a)/a ≤ (2 + 1/b)/b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hdiff : (2 + 1/a)/a - (2 + 1/b)/b = (1/a - 1/b) * (2 + 1/a + 1/b) := by
    field_simp; ring
  have h1 : 1 / a ≤ 1 / b := one_div_le_one_div_of_le hb hba
  have h3 : (1/a - 1/b) * (2 + 1/a + 1/b) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  linarith [hdiff, h3]

/-- `uAb t = 1/(t log t)` is antitone for `t > 1`. -/
lemma uAb_anti {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : uAb b ≤ uAb a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  rw [uAb, uAb]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul hab hlab (le_of_lt hla) (le_of_lt hb0)

/-! ### The main comparison -/

theorem abJbd_le_abJ (z : ℕ) (hz : 30000 ≤ z) (hz2 : z ≤ 10 ^ 5) :
    Work.RHContract.A.RegionII.abJbd ≤ Work.RHContract.A.RegionII.abJ z := by
  -- basic size facts about `z`
  have hzR : (30000:ℝ) ≤ z := by exact_mod_cast hz
  have hz100 : (z:ℝ) ≤ 10^5 := by exact_mod_cast hz2
  have hzpos : (0:ℝ) < z := by linarith
  have hlogzpos : 0 < Real.log (z:ℝ) := Real.log_pos (by linarith)
  have hlg30000lpos : 0 < lg30000l := by rw [lg30000l]; norm_num
  have hlg501lpos : 0 < lg501l := by rw [lg501l]; norm_num
  have hlg512upos : 0 < lg512u := by rw [lg512u]; norm_num
  have hlg100kupos : 0 < lg100ku := by rw [lg100ku]; norm_num
  have hsq501lpos : 0 < sq501l := by rw [sq501l]; norm_num
  have hlog501pos : 0 < Real.log 501 := Real.log_pos (by norm_num : (1:ℝ) < 501)
  -- log bounds at `z`
  have hlogz_le : Real.log (z:ℝ) ≤ lg100ku :=
    le_trans (Real.log_le_log hzpos hz100) log100k_ub
  have hlogz_ge : lg30000l ≤ Real.log (z:ℝ) :=
    le_trans log30000_lb
      (Real.log_le_log (by norm_num : (0:ℝ) < 30000) hzR)
  -- the common denominator bound `z log z ≤ 10^5 · lg100ku`
  have hden_le : (z:ℝ) * Real.log z ≤ 10^5 * lg100ku :=
    mul_le_mul hz100 hlogz_le (le_of_lt hlogzpos) (by norm_num)
  -- ### term 1
  have h1term : (96/100)/(10^5 * lg100ku) ≤ (96/100)/((z:ℝ) * Real.log z) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 96/100)
      (mul_pos hzpos hlogzpos)
    exact hden_le
  -- ### term 2 ingredients
  have hu501l : u501l ≤ uAb 501 := by
    rw [u501l, uAb]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hlog501pos)
    have h512 : Real.log (501:ℝ) ≤ lg512u :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num : (501:ℝ) ≤ 512)) log512_ub
    nlinarith [h512]
  have huzu : uAb (z:ℝ) ≤ uzu := by
    rw [uzu, uAb]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hlg30000lpos)
    exact mul_le_mul hzR hlogz_ge (le_of_lt hlg30000lpos) (by norm_num)
  have h2term : 2 * (u501l - uzu) ≤ 2 * (uAb 501 - uAb (z:ℝ)) := by
    linarith [hu501l, huzu]
  -- ### term 3 ingredients
  have hu501u : uAb 501 ≤ u501u := by
    rw [u501u, uAb]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hlg501lpos)
    nlinarith [log501_lb]
  have huzl : uzl ≤ uAb (z:ℝ) := by
    rw [uzl, uAb]
    apply one_div_le_one_div_of_le (mul_pos hzpos hlogzpos)
    exact hden_le
  have hAbz_le_501 : uAb (z:ℝ) ≤ uAb 501 :=
    uAb_anti (by norm_num : (1:ℝ) < 501)
      (by exact_mod_cast (by omega : 501 ≤ z))
  have hA : uAb 501 - uAb (z:ℝ) ≤ u501u - uzl := by linarith [hu501u, huzl]
  have hA' : 0 ≤ u501u - uzl := by linarith [hu501u, huzl, hAbz_le_501]
  have h3term : (uAb 501 - uAb (z:ℝ))/(Real.log 501 + 1) ≤ (u501u - uzl)/(lg501l + 1) := by
    have hd1 : 0 < Real.log 501 + 1 := by linarith
    have hd2 : 0 < lg501l + 1 := by linarith
    have hle1 : (uAb 501 - uAb (z:ℝ))/(Real.log 501 + 1)
        ≤ (u501u - uzl)/(Real.log 501 + 1) := by
      rw [div_le_div_iff_of_pos_right hd1]; exact hA
    have hle2 : (u501u - uzl)/(Real.log 501 + 1)
        ≤ (u501u - uzl)/(lg501l + 1) := by
      apply div_le_div_of_nonneg_left hA' hd2
      linarith [log501_lb]
    linarith [hle1, hle2]
  -- ### term 4 ingredients
  have hz501 : (501:ℝ) ≤ z := by exact_mod_cast (by omega : 501 ≤ z)
  have hchi : chAb 501 ≤ chi501u := by
    have h := chi_anti (a := Real.log 501) (b := lg501l) hlg501lpos log501_lb
    simpa [chAb, chi501u] using h
  have hchi501u_nonneg : 0 ≤ chi501u := by rw [chi501u]; positivity
  have hchAb_nonneg : 0 ≤ chAb 501 := by rw [chAb]; positivity
  have hbr_nonneg : 0 ≤ 1/(501 * Real.sqrt 501) - 1/((z:ℝ) * Real.sqrt z) := by
    have hzsqrt : (501:ℝ) * Real.sqrt 501 ≤ (z:ℝ) * Real.sqrt z :=
      mul_le_mul hz501 (Real.sqrt_le_sqrt hz501) (Real.sqrt_nonneg _) (by linarith)
    have hpos501 : (0:ℝ) < 501 * Real.sqrt 501 :=
      mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
    have h := one_div_le_one_div_of_le hpos501 hzsqrt
    linarith
  have hbr_ub : 1/(501 * Real.sqrt 501) - 1/((z:ℝ) * Real.sqrt z) ≤ inv501_32_ub := by
    have hzsinv : 0 ≤ 1/((z:ℝ) * Real.sqrt z) := by
      apply div_nonneg (by norm_num)
      exact mul_nonneg (le_of_lt hzpos) (Real.sqrt_nonneg _)
    have hstep1 : 1/(501 * Real.sqrt 501) - 1/((z:ℝ) * Real.sqrt z)
        ≤ 1/(501 * Real.sqrt 501) := by linarith
    have hstep2 : 1/(501 * Real.sqrt 501) ≤ inv501_32_ub := by
      rw [inv501_32_ub]
      apply one_div_le_one_div_of_le (mul_pos (by norm_num) hsq501lpos)
      nlinarith [sq501_lb]
    linarith
  have hprod : chAb 501 * (1/(501 * Real.sqrt 501) - 1/((z:ℝ) * Real.sqrt z))
      ≤ chi501u * inv501_32_ub :=
    mul_le_mul hchi hbr_ub hbr_nonneg hchi501u_nonneg
  have h4term : (23/10) * chAb 501 * (2/3)
        * (1/(501 * Real.sqrt 501) - 1/((z:ℝ) * Real.sqrt z))
      ≤ (23/10) * chi501u * (2/3) * inv501_32_ub := by
    have hc : (0:ℝ) ≤ (23/10) * (2/3) := by norm_num
    have h := mul_le_mul_of_nonneg_left hprod hc
    nlinarith [h]
  -- ### assemble
  rw [Work.RHContract.A.RegionII.abJbd, Work.RHContract.A.RegionII.abJ]
  linarith [h1term, h2term, h3term, h4term]

end Work.RHContract.A.regionII
