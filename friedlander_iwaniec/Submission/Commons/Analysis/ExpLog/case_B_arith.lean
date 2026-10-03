import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.ExpLog.log_band_tail

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.Analysis.ExpLog

/-- For `b > 0` and `x ≥ 0`, `x ^ n * exp (-(b * x)) ≤ (n / (b * e)) ^ n`. -/
lemma caseB_pow_mul_exp_neg_le (n : ℕ) {b : ℝ} (hb : 0 < b) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-(b * x)) ≤ ((n : ℝ) / (b * Real.exp 1)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, pow_zero, one_mul]
    have h1 : -(b * x) ≤ 0 := by nlinarith [mul_nonneg hb.le hx]
    calc Real.exp (-(b * x)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h1
      _ = 1 := Real.exp_zero
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hbnne : b ≠ 0 := ne_of_gt hb
  set a : ℝ := b * x / (n : ℝ) with ha_def
  have hkey0 : x * Real.exp (-a) ≤ (n : ℝ) / (b * Real.exp 1) := by
    have h1 : a * Real.exp (-a) ≤ (Real.exp 1)⁻¹ := by
      simpa [Real.exp_neg] using Real.mul_exp_neg_le_exp_neg_one a
    have h2 : ((n : ℝ) / b) * (a * Real.exp (-a)) ≤ ((n : ℝ) / b) * (Real.exp 1)⁻¹ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((n : ℝ) / b) * (a * Real.exp (-a)) = x * Real.exp (-a) := by
      rw [ha_def]
      field_simp [hbnne, hnne]
    have h4 : ((n : ℝ) / b) * (Real.exp 1)⁻¹ = (n : ℝ) / (b * Real.exp 1) := by
      rw [div_eq_mul_inv]; ring
    linarith [h2, h3, h4]
  have hkey : x ≤ ((n : ℝ) / (b * Real.exp 1)) * Real.exp a := by
    have hxeq : (x * Real.exp (-a)) * Real.exp a = x := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [← hxeq]
    exact mul_le_mul_of_nonneg_right hkey0 (Real.exp_pos a).le
  have hpow := pow_le_pow_left₀ hx hkey n
  rw [mul_pow] at hpow
  have hexp : Real.exp a ^ n = Real.exp (b * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [ha_def]
    field_simp
  rw [hexp] at hpow
  have hstep := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(b * x))).le
  have heq : ((n : ℝ) / (b * Real.exp 1)) ^ n * Real.exp (b * x) * Real.exp (-(b * x)) =
      ((n : ℝ) / (b * Real.exp 1)) ^ n := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rwa [heq] at hstep

/-- For `x ≥ 48`, `3 * x ≤ exp (x/2)`. -/
lemma caseB_three_mul_le_exp_half {x : ℝ} (hx : 48 ≤ x) : 3 * x ≤ Real.exp (x / 2) := by
  have h := exp_ge_sq_div_four (x / 2) (by linarith)
  have h2 : (x / 2) ^ 2 / 4 = x ^ 2 / 16 := by ring
  rw [h2] at h
  have h3 : 3 * x ≤ x ^ 2 / 16 := by nlinarith
  linarith [h, h3]

/-- For `v ≥ 48`, `v^2 * exp (-(exp (v/2))) ≤ 1`. -/
lemma caseB_sq_mul_exp_neg_exp_half_le_one {v : ℝ} (hv : 48 ≤ v) :
    v ^ 2 * Real.exp (-(Real.exp (v / 2))) ≤ 1 := by
  have hv0 : 0 < v := by linarith
  have h1 : 3 * v ≤ Real.exp (v / 2) := caseB_three_mul_le_exp_half hv
  have h2 : Real.exp (3 * v) ≤ Real.exp (Real.exp (v / 2)) := Real.exp_le_exp.mpr h1
  have h3 : v ^ 2 ≤ Real.exp (3 * v) := by
    have h := exp_ge_sq_div_four (3 * v) (by linarith)
    have h4 : (3 * v) ^ 2 / 4 = 9 * v ^ 2 / 4 := by ring
    rw [h4] at h
    nlinarith [h]
  have hE : 0 < Real.exp (Real.exp (v / 2)) := Real.exp_pos _
  have hle : v ^ 2 ≤ Real.exp (Real.exp (v / 2)) := le_trans h3 h2
  calc v ^ 2 * Real.exp (-(Real.exp (v / 2)))
      = v ^ 2 * (Real.exp (Real.exp (v / 2)))⁻¹ := by rw [Real.exp_neg]
    _ ≤ Real.exp (Real.exp (v / 2)) * (Real.exp (Real.exp (v / 2)))⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hE.le)
    _ = 1 := by rw [mul_inv_cancel₀ hE.ne']

/-- For `z ≥ 10^6` and `1 / c0 ≤ z / 10^6` (with `0 < c0`),
`(z / c0)^3 * exp (-(z * exp (z/2) / 4)) ≤ 1`. -/
lemma caseB_factor1_bound {c0 z : ℝ} (hc0 : 0 < c0) (hz : (1000000 : ℝ) ≤ z)
    (hcz : 1 / c0 ≤ z / 1000000) :
    (z / c0) ^ 3 * Real.exp (-(z * Real.exp (z / 2) / 4)) ≤ 1 := by
  have hz0 : 0 < z := by linarith
  have hz1000 : (1000 : ℝ) ≤ z := by linarith
  have hlogz : Real.log z ≤ z / 8 := log_le_div_eight_of_ge z hz1000
  have hlogc : Real.log (1 / c0) ≤ 1 / c0 := by
    have h1 : Real.log (1 / c0) ≤ 1 / c0 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlogzc : Real.log (z / c0) = Real.log z + Real.log (1 / c0) := by
    rw [Real.log_div hz0.ne' hc0.ne', one_div, Real.log_inv]
    ring
  have hbound : Real.log z + Real.log (1 / c0) ≤ z / 4 := by
    have h2 : z / 8 + z / 1000000 ≤ z / 4 := by nlinarith
    linarith [hlogz, hlogc, hcz, h2]
  have hlog : 3 * Real.log (z / c0) ≤ 3 * (z / 4) := by
    rw [hlogzc]; linarith [hbound]
  have hexp3 : 3 ≤ Real.exp (z / 2) := by
    have h := exp_ge_sq_div_four (z / 2) (by linarith)
    have h2 : (z / 2) ^ 2 / 4 = z ^ 2 / 16 := by ring
    rw [h2] at h
    nlinarith [h, hz0]
  have hmain : 3 * Real.log (z / c0) ≤ z * Real.exp (z / 2) / 4 := by
    have h1 : 3 * (z / 4) ≤ z * Real.exp (z / 2) / 4 := by nlinarith [hexp3, hz0]
    linarith [hlog, h1]
  have h1 : (z / c0) ^ 3 ≤ Real.exp (z * Real.exp (z / 2) / 4) := by
    have h2 : (z / c0) ^ 3 = Real.exp (3 * Real.log (z / c0)) := by
      calc (z / c0) ^ 3 = Real.exp (Real.log ((z / c0) ^ 3)) := (Real.exp_log (by positivity)).symm
        _ = Real.exp (3 * Real.log (z / c0)) := by rw [Real.log_pow]; norm_num
    rw [h2]
    exact Real.exp_le_exp.mpr hmain
  calc (z / c0) ^ 3 * Real.exp (-(z * Real.exp (z / 2) / 4))
      ≤ Real.exp (z * Real.exp (z / 2) / 4) * Real.exp (-(z * Real.exp (z / 2) / 4)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

theorem case_B_arith (c0 Kp : ℝ) (hc0 : 0 < c0) (hc0le : c0 ≤ 1) (hKp : 0 < Kp) :
    ∃ K Z0 : ℝ, 0 ≤ K ∧ 3 ≤ Z0 ∧ ∀ z w : ℝ, Z0 ≤ z → 3 ≤ w → z ^ 2 ≤ w →
      Real.log z < Real.log w / Real.log z →
      Kp * ((Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
          * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 21)
          * Real.exp (-(c0 * (Real.log w / Real.log z) * Real.log z
              / (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 22)))
        + (Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
          / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20)
        + 3 * (Real.log w + 1) / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20))
      ≤ K * z ^ (-(c0 / 16)) := by
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0
  have hc0sqle : c0 ^ 2 ≤ 1 := by nlinarith [hc0, hc0le]
  set KA1 : ℝ := 9 * c0 ^ 2 * (240 / (13 * c0 * Real.exp 1)) ^ 5 with hKA1
  set KB : ℝ := 3 * Real.exp (-20) * (48 / (15 * c0 * Real.exp 1)) ^ 3 with hKB
  set KC : ℝ := 4 * Real.exp (-20) * (16 / (15 * c0 * Real.exp 1)) with hKC
  set K0 : ℝ := KA1 + 9 + KB + KC with hK0
  set L0 : ℝ := 1000000 / c0 ^ 2 with hL0
  refine ⟨Kp * K0, max 3 (Real.exp L0), ?_, ?_, ?_⟩
  · rw [hK0, hKA1, hKB, hKC]; positivity
  · exact le_max_left _ _
  · intro z w hz hw hzw hcond
    have hz3 : (3:ℝ) ≤ z := le_trans (le_max_left _ _) hz
    have hz0 : 0 < z := by linarith
    have hw0 : 0 < w := by linarith
    have hZ0z : Real.exp L0 ≤ z := le_trans (le_max_right _ _) hz
    have hL0le : L0 ≤ Real.log z := by
      have h := Real.log_le_log (Real.exp_pos L0) hZ0z
      rwa [Real.log_exp] at h
    set L : ℝ := Real.log z with hL
    set M : ℝ := Real.log w with hM
    set t : ℝ := M / L with ht
    set v : ℝ := Real.log t with hv
    set X : ℝ := c0 * L + v with hX
    have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
    have hMpos : 0 < M := by rw [hM]; exact Real.log_pos (by linarith)
    have htpos : 0 < t := by rw [ht]; exact div_pos hMpos hLpos
    have hLge : (1000000:ℝ) ≤ L := by
      have h1 : (1000000:ℝ) ≤ L0 := by
        rw [hL0, le_div_iff₀ (by positivity : (0:ℝ) < c0^2)]
        nlinarith [hc0sqle]
      linarith
    have hcLge : (1000000:ℝ) ≤ c0 * L := by
      have h1 : c0 * L0 = 1000000 / c0 := by rw [hL0]; field_simp
      have h2 : (1000000:ℝ) ≤ 1000000 / c0 := by
        rw [le_div_iff₀ hc0]; nlinarith [hc0le]
      have h3 : c0 * L0 ≤ c0 * L := mul_le_mul_of_nonneg_left hL0le hc0.le
      linarith
    have ht1 : 1 ≤ t := by linarith [hcond, hLge]
    have hML : M = t * L := by rw [ht]; field_simp
    have hvnn : 0 ≤ v := by rw [hv]; exact Real.log_nonneg ht1
    have hexpt : t = Real.exp v := by rw [hv, Real.exp_log htpos]
    have hzrpow : z ^ (-(c0 / 16)) = Real.exp (-(c0 / 16) * L) := by
      rw [Real.rpow_def_of_pos hz0, ← hL]
      congr 1
      ring
    have htinv : Real.exp (-v) = 1 / t := by
      rw [hv, Real.exp_neg, Real.exp_log htpos]; ring
    -- Term A bound
    have hA : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
        ≤ (KA1 + 9) * Real.exp (-(c0 / 16) * L) := by
      have hcase : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
            * Real.exp ((c0 / 16) * L) ≤ KA1 + 9 := by
        by_cases hvle : v ≤ c0 * L
        · -- region (a): log t ≤ c0 log z
          have hDle : X + 22 ≤ 3 * (c0 * L) := by rw [hX]; linarith
          have hDpos : 0 < X + 22 := by rw [hX]; linarith [hcLge, hvnn]
          have hDnn : 0 ≤ X + 22 := le_of_lt hDpos
          have hfrac : 1 / 3 ≤ t / (X + 22) := by
            rw [le_div_iff₀ hDpos]
            have h1 : (1/3) * (X + 22) ≤ (1/3) * (3 * (c0 * L)) := by linarith [hDle]
            have h2 : (1/3) * (3 * (c0 * L)) = c0 * L := by ring
            have h3 : c0 * L ≤ t := by
              have hc0Lle : c0 * L ≤ L := by nlinarith [hc0le, hLpos]
              linarith [hc0Lle, hcond]
            linarith [h1, h2, h3]
          have hexparg : -(c0 * t * L / (X + 22)) + (c0 / 16) * L ≤ -(13 * c0 * L / 48) := by
            have hcLnn : 0 ≤ c0 * L := by linarith [hcLge]
            have hmul : (c0 * L) * (1/3) ≤ (c0 * L) * (t / (X + 22)) :=
              mul_le_mul_of_nonneg_left hfrac hcLnn
            have hE : c0 * t * L / (X + 22) = (c0 * L) * (t / (X + 22)) := by ring_nf
            rw [hE]
            nlinarith [hmul]
          have hprod_le : L ^ 3 * (X + 23) * (X + 21) ≤ 9 * c0 ^ 2 * L ^ 5 := by
            have h1 : (X + 23) * (X + 21) ≤ (X + 22) ^ 2 := by nlinarith
            have h2 : (X + 22) ^ 2 ≤ (3 * (c0 * L)) ^ 2 := pow_le_pow_left₀ hDnn hDle 2
            have h3 : (3 * (c0 * L)) ^ 2 = 9 * c0 ^ 2 * L ^ 2 := by ring
            have h4 : (X + 23) * (X + 21) ≤ 9 * c0 ^ 2 * L ^ 2 := by rw [← h3]; linarith
            calc L ^ 3 * (X + 23) * (X + 21) = L ^ 3 * ((X + 23) * (X + 21)) := by ring
              _ ≤ L ^ 3 * (9 * c0 ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
              _ = 9 * c0 ^ 2 * L ^ 5 := by ring
          have hnn : 0 ≤ L ^ 3 * (X + 23) * (X + 21) := by
            have h1 : 0 ≤ X + 23 := by linarith [hDpos]
            have h2 : 0 ≤ X + 21 := by linarith [hDpos]
            positivity
          have hexpstep : Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)
              ≤ Real.exp (-(13 * c0 * L / 48)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr hexparg
          have hp : L ^ 5 * Real.exp (-(13 * c0 * L / 48))
              ≤ ((5 : ℝ) / (13 * c0 / 48 * Real.exp 1)) ^ 5 := by
            have h := caseB_pow_mul_exp_neg_le 5 (b := 13 * c0 / 48) (by positivity) hLpos.le
            simpa [show 13 * c0 / 48 * L = 13 * c0 * L / 48 by ring] using h
          have h3c : (5 : ℝ) / (13 * c0 / 48 * Real.exp 1) = 240 / (13 * c0 * Real.exp 1) := by
            ring_nf
          have hbound : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
              * Real.exp ((c0 / 16) * L) ≤ 9 * c0 ^ 2 * (240 / (13 * c0 * Real.exp 1)) ^ 5 := by
            have hstep : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
                * Real.exp ((c0 / 16) * L)
                = L ^ 3 * (X + 23) * (X + 21)
                    * (Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)) := by ring
            calc L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
                  * Real.exp ((c0 / 16) * L)
                = L ^ 3 * (X + 23) * (X + 21)
                    * (Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)) := hstep
              _ ≤ L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(13 * c0 * L / 48)) :=
                  mul_le_mul_of_nonneg_left hexpstep hnn
              _ = (L ^ 3 * (X + 23) * (X + 21)) * Real.exp (-(13 * c0 * L / 48)) := by ring
              _ ≤ (9 * c0 ^ 2 * L ^ 5) * Real.exp (-(13 * c0 * L / 48)) :=
                  mul_le_mul_of_nonneg_right hprod_le (Real.exp_pos _).le
              _ = 9 * c0 ^ 2 * (L ^ 5 * Real.exp (-(13 * c0 * L / 48))) := by ring
              _ ≤ 9 * c0 ^ 2 * ((5 : ℝ) / (13 * c0 / 48 * Real.exp 1)) ^ 5 :=
                  mul_le_mul_of_nonneg_left hp (by positivity)
              _ = 9 * c0 ^ 2 * (240 / (13 * c0 * Real.exp 1)) ^ 5 := by rw [h3c]
          rw [hKA1]
          linarith [hbound]
        · -- region (b): c0 log z < log t
          have hvgt : c0 * L < v := lt_of_not_ge hvle
          have hv48 : 48 ≤ v := by linarith [hcLge]
          have hDle : X + 22 ≤ 3 * v := by rw [hX]; linarith [hvgt]
          have hDpos : 0 < X + 22 := by rw [hX]; linarith [hcLge, hvnn]
          have hDnn : 0 ≤ X + 22 := le_of_lt hDpos
          have hfrac : Real.exp (v / 2) ≤ t / (X + 22) := by
            have h1 : Real.exp v / (3 * v) ≤ t / (X + 22) := by
              have h := mul_le_mul_of_nonneg_left hDle (Real.exp_pos v).le
              rw [hexpt]
              rw [le_div_iff₀ hDpos, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 3 * v)]
              linarith [h]
            have h2 : Real.exp (v / 2) ≤ Real.exp v / (3 * v) := by
              rw [le_div_iff₀ (by linarith : (0:ℝ) < 3 * v)]
              have h3 : 3 * v ≤ Real.exp (v / 2) := caseB_three_mul_le_exp_half hv48
              have h4 : Real.exp v = Real.exp (v / 2) * Real.exp (v / 2) := by
                rw [← Real.exp_add]; ring_nf
              rw [h4]
              nlinarith [h3, Real.exp_pos (v/2)]
            linarith [h1, h2]
          have hexparg : -(c0 * t * L / (X + 22)) + (c0 / 16) * L
              ≤ -(c0 * L * Real.exp (v / 2) / 2) := by
            have hcLnn : 0 ≤ c0 * L := by linarith [hcLge]
            have hmul : (c0 * L) * Real.exp (v / 2) ≤ (c0 * L) * (t / (X + 22)) :=
              mul_le_mul_of_nonneg_left hfrac hcLnn
            have hev : 1 / 8 ≤ Real.exp (v / 2) := by
              have h := Real.one_le_exp (by linarith : (0:ℝ) ≤ v / 2); linarith
            have hE : c0 * t * L / (X + 22) = (c0 * L) * (t / (X + 22)) := by ring_nf
            rw [hE]
            nlinarith [hmul, hev, hcLnn]
          have hprod_le : L ^ 3 * (X + 23) * (X + 21) ≤ 9 * L ^ 3 * v ^ 2 := by
            have h1 : (X + 23) * (X + 21) ≤ (X + 22) ^ 2 := by nlinarith
            have h2 : (X + 22) ^ 2 ≤ (3 * v) ^ 2 := pow_le_pow_left₀ hDnn hDle 2
            have h3 : (3 * v) ^ 2 = 9 * v ^ 2 := by ring
            have h4 : (X + 23) * (X + 21) ≤ 9 * v ^ 2 := by rw [← h3]; linarith
            calc L ^ 3 * (X + 23) * (X + 21) = L ^ 3 * ((X + 23) * (X + 21)) := by ring
              _ ≤ L ^ 3 * (9 * v ^ 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
              _ = 9 * L ^ 3 * v ^ 2 := by ring
          have hnn : 0 ≤ L ^ 3 * (X + 23) * (X + 21) := by
            have h1 : 0 ≤ X + 23 := by linarith [hDpos]
            have h2 : 0 ≤ X + 21 := by linarith [hDpos]
            positivity
          have hexpstep : Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)
              ≤ Real.exp (-(c0 * L * Real.exp (v / 2) / 2)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr hexparg
          have hsplit : Real.exp (-(c0 * L * Real.exp (v / 2) / 2))
              = Real.exp (-(c0 * L * Real.exp (v / 2) / 4))
                * Real.exp (-(c0 * L * Real.exp (v / 2) / 4)) := by
            rw [← Real.exp_add]; congr 1; ring
          have hF1 : L ^ 3 * Real.exp (-(c0 * L * Real.exp (v / 2) / 4)) ≤ 1 := by
            have hmono : Real.exp (-(c0 * L * Real.exp (v / 2) / 4))
                ≤ Real.exp (-(c0 * L * Real.exp (c0 * L / 2) / 4)) := by
              apply Real.exp_le_exp.mpr
              have h : Real.exp (c0 * L / 2) ≤ Real.exp (v / 2) := Real.exp_le_exp.mpr (by linarith)
              nlinarith [h, Real.exp_pos (v/2)]
            have hcz : 1 / c0 ≤ (c0 * L) / 1000000 := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1000000)]
              have hL0eq : c0 ^ 2 * L0 = 1000000 := by rw [hL0]; field_simp
              have hle : c0 ^ 2 * L0 ≤ c0 ^ 2 * L := mul_le_mul_of_nonneg_left hL0le (by positivity)
              have hge : (1000000:ℝ) ≤ c0 ^ 2 * L := by rw [← hL0eq]; exact hle
              field_simp
              nlinarith [hge]
            have hf1 := caseB_factor1_bound hc0 hcLge hcz
            have hzeq : (c0 * L) / c0 = L := by field_simp
            rw [hzeq] at hf1
            calc L ^ 3 * Real.exp (-(c0 * L * Real.exp (v / 2) / 4))
                ≤ L ^ 3 * Real.exp (-(c0 * L * Real.exp (c0 * L / 2) / 4)) :=
                  mul_le_mul_of_nonneg_left hmono (by positivity)
              _ ≤ 1 := hf1
          have hF2 : v ^ 2 * Real.exp (-(c0 * L * Real.exp (v / 2) / 4)) ≤ 1 := by
            have h4 : (4:ℝ) ≤ c0 * L := by linarith [hcLge]
            have hmono : Real.exp (-(c0 * L * Real.exp (v / 2) / 4)) ≤ Real.exp (-(Real.exp (v / 2))) := by
              apply Real.exp_le_exp.mpr
              have : 4 * Real.exp (v / 2) ≤ c0 * L * Real.exp (v / 2) := by
                nlinarith [Real.exp_pos (v/2)]
              linarith
            exact le_trans (mul_le_mul_of_nonneg_left hmono (by positivity))
              (caseB_sq_mul_exp_neg_exp_half_le_one hv48)
          have hprod2 : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
                * Real.exp ((c0 / 16) * L) ≤ 9 := by
            have hstep : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
                  * Real.exp ((c0 / 16) * L)
                = L ^ 3 * (X + 23) * (X + 21)
                    * (Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)) := by ring
            calc L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
                  * Real.exp ((c0 / 16) * L)
                = L ^ 3 * (X + 23) * (X + 21)
                    * (Real.exp (-(c0 * t * L / (X + 22))) * Real.exp ((c0 / 16) * L)) := hstep
              _ ≤ L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * L * Real.exp (v / 2) / 2)) :=
                  mul_le_mul_of_nonneg_left hexpstep hnn
              _ ≤ (9 * L ^ 3 * v ^ 2) * Real.exp (-(c0 * L * Real.exp (v / 2) / 2)) :=
                  mul_le_mul_of_nonneg_right hprod_le (Real.exp_pos _).le
              _ = 9 * ((L ^ 3 * Real.exp (-(c0 * L * Real.exp (v / 2) / 4)))
                    * (v ^ 2 * Real.exp (-(c0 * L * Real.exp (v / 2) / 4)))) := by
                  rw [hsplit]; ring
              _ ≤ 9 * (1 * 1) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hF1 hF2 (by positivity) (by norm_num)) (by norm_num)
              _ = 9 := by ring
          have hKA1nn : 0 ≤ KA1 := by rw [hKA1]; positivity
          linarith [hprod2, hKA1nn]
      have hpos : 0 < Real.exp ((c0 / 16) * L) := Real.exp_pos _
      have hh := (le_div_iff₀ hpos).mpr hcase
      have heq : (KA1 + 9) / Real.exp ((c0 / 16) * L)
          = (KA1 + 9) * Real.exp (-(c0 / 16) * L) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        ring
      rwa [heq] at hh
    -- Term B bound
    have hB : L ^ 3 * (X + 23) / Real.exp (X + 20) ≤ KB * Real.exp (-(c0 / 16) * L) := by
      have hX23 : (X + 23) / t ≤ 3 := by
        have h1 : c0 * L / t < 1 := by
          rw [div_lt_one htpos]
          have hc0Lle : c0 * L ≤ L := by nlinarith [hc0le, hLpos]
          linarith [hc0Lle, hcond]
        have h2 : v / t ≤ 1 := by
          rw [hv, div_le_one htpos]
          have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
          linarith
        have h3 : 23 / t ≤ 1 := by
          rw [div_le_one htpos]; linarith [hcond, hLge]
        have hsum : (X + 23) / t = c0 * L / t + v / t + 23 / t := by rw [hX]; ring_nf
        rw [hsum]; linarith
      have hexpB : Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)
          = Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-v) * Real.exp (-20) := by
        have harg : -(X + 20) + (c0 / 16) * L = -(15 * c0 / 16 * L) + (-v) + (-20) := by
          rw [hX]; ring
        calc Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)
            = Real.exp (-(X + 20) + (c0 / 16) * L) := by rw [Real.exp_add]
          _ = Real.exp (-(15 * c0 / 16 * L) + (-v) + (-20)) := by rw [harg]
          _ = Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-v) * Real.exp (-20) := by
              rw [Real.exp_add, Real.exp_add]
      have hmain : L ^ 3 * (X + 23) / Real.exp (X + 20) * Real.exp ((c0 / 16) * L) ≤ KB := by
        have step1 : L ^ 3 * (X + 23) / Real.exp (X + 20) * Real.exp ((c0 / 16) * L)
            = L ^ 3 * (X + 23) * (Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)) := by
          rw [div_eq_mul_inv, Real.exp_neg]; ring
        have step2 : L ^ 3 * (X + 23) * (Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L))
            = L ^ 3 * (X + 23) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20) := by
          rw [hexpB, htinv]; ring
        have step3 : L ^ 3 * (X + 23) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)
            ≤ 3 * Real.exp (-20) * (L ^ 3 * Real.exp (-(15 * c0 / 16 * L))) := by
          have h1 : L ^ 3 * (X + 23) * (1 / t) ≤ 3 * L ^ 3 := by
            rw [show L ^ 3 * (X + 23) * (1 / t) = L ^ 3 * ((X + 23) / t) by ring_nf]
            calc L ^ 3 * ((X + 23) / t) ≤ L ^ 3 * 3 :=
                  mul_le_mul_of_nonneg_left hX23 (by positivity)
              _ = 3 * L ^ 3 := by ring
          calc L ^ 3 * (X + 23) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)
              = (L ^ 3 * (X + 23) * (1 / t))
                  * (Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)) := by ring
            _ ≤ (3 * L ^ 3) * (Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = 3 * Real.exp (-20) * (L ^ 3 * Real.exp (-(15 * c0 / 16 * L))) := by ring
        have hb3 : L ^ 3 * Real.exp (-(15 * c0 / 16 * L))
            ≤ ((3 : ℝ) / (15 * c0 / 16 * Real.exp 1)) ^ 3 := by
          have h := caseB_pow_mul_exp_neg_le 3 (b := 15 * c0 / 16) (by positivity) hLpos.le
          simpa using h
        have step4 : 3 * Real.exp (-20) * (L ^ 3 * Real.exp (-(15 * c0 / 16 * L)))
            ≤ 3 * Real.exp (-20) * ((3 : ℝ) / (15 * c0 / 16 * Real.exp 1)) ^ 3 :=
          mul_le_mul_of_nonneg_left hb3 (by positivity)
        have hKBv : 3 * Real.exp (-20) * ((3 : ℝ) / (15 * c0 / 16 * Real.exp 1)) ^ 3 = KB := by
          rw [hKB]
          have h3 : (3 : ℝ) / (15 * c0 / 16 * Real.exp 1) = 48 / (15 * c0 * Real.exp 1) := by ring_nf
          rw [h3]
        rw [step1, step2]
        linarith [step3, step4, hKBv]
      have hpos : 0 < Real.exp ((c0 / 16) * L) := Real.exp_pos _
      have hh := (le_div_iff₀ hpos).mpr hmain
      have heq : KB / Real.exp ((c0 / 16) * L) = KB * Real.exp (-(c0 / 16) * L) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        ring
      rwa [heq] at hh
    -- Term C bound
    have hC : 3 * (M + 1) / Real.exp (X + 20) ≤ KC * Real.exp (-(c0 / 16) * L) := by
      have hexpC : Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)
          = Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-v) * Real.exp (-20) := by
        have harg : -(X + 20) + (c0 / 16) * L = -(15 * c0 / 16 * L) + (-v) + (-20) := by
          rw [hX]; ring
        calc Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)
            = Real.exp (-(X + 20) + (c0 / 16) * L) := by rw [Real.exp_add]
          _ = Real.exp (-(15 * c0 / 16 * L) + (-v) + (-20)) := by rw [harg]
          _ = Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-v) * Real.exp (-20) := by
              rw [Real.exp_add, Real.exp_add]
      have hmain : 3 * (M + 1) / Real.exp (X + 20) * Real.exp ((c0 / 16) * L) ≤ KC := by
        have step1 : 3 * (M + 1) / Real.exp (X + 20) * Real.exp ((c0 / 16) * L)
            = 3 * (M + 1) * (Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L)) := by
          rw [div_eq_mul_inv, Real.exp_neg]; ring
        have step2 : 3 * (M + 1) * (Real.exp (-(X + 20)) * Real.exp ((c0 / 16) * L))
            = 3 * (M + 1) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20) := by
          rw [hexpC, htinv]; ring
        have hMt : 3 * (M + 1) * (1 / t) ≤ 4 * L := by
          have h1 : 3 * (M + 1) * (1 / t) = 3 * L + 3 / t := by rw [hML]; field_simp
          have h2 : 3 / t ≤ 3 / L := by
            rw [div_le_div_iff₀ htpos hLpos]; linarith [hcond]
          have h3 : 3 / L ≤ 3 := by rw [div_le_iff₀ hLpos]; linarith [hLge]
          linarith [h1, h2, h3, hLge]
        have step3 : 3 * (M + 1) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)
            ≤ 4 * Real.exp (-20) * (L * Real.exp (-(15 * c0 / 16 * L))) := by
          calc 3 * (M + 1) * (1 / t) * Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)
              = (3 * (M + 1) * (1 / t))
                  * (Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)) := by ring
            _ ≤ (4 * L) * (Real.exp (-(15 * c0 / 16 * L)) * Real.exp (-20)) :=
                mul_le_mul_of_nonneg_right hMt (by positivity)
            _ = 4 * Real.exp (-20) * (L * Real.exp (-(15 * c0 / 16 * L))) := by ring
        have hb1 : L * Real.exp (-(15 * c0 / 16 * L))
            ≤ (1 : ℝ) / (15 * c0 / 16 * Real.exp 1) := by
          have h := caseB_pow_mul_exp_neg_le 1 (b := 15 * c0 / 16) (by positivity) hLpos.le
          simpa using h
        have step4 : 4 * Real.exp (-20) * (L * Real.exp (-(15 * c0 / 16 * L)))
            ≤ 4 * Real.exp (-20) * ((1 : ℝ) / (15 * c0 / 16 * Real.exp 1)) :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
        have hKCv : 4 * Real.exp (-20) * ((1 : ℝ) / (15 * c0 / 16 * Real.exp 1)) = KC := by
          rw [hKC]
          have h3 : (1 : ℝ) / (15 * c0 / 16 * Real.exp 1) = 16 / (15 * c0 * Real.exp 1) := by ring_nf
          rw [h3]
        rw [step1, step2]
        linarith [step3, step4, hKCv]
      have hpos : 0 < Real.exp ((c0 / 16) * L) := Real.exp_pos _
      have hh := (le_div_iff₀ hpos).mpr hmain
      have heq : KC / Real.exp ((c0 / 16) * L) = KC * Real.exp (-(c0 / 16) * L) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        ring
      rwa [heq] at hh
    have hsum : L ^ 3 * (X + 23) * (X + 21) * Real.exp (-(c0 * t * L / (X + 22)))
        + L ^ 3 * (X + 23) / Real.exp (X + 20)
        + 3 * (M + 1) / Real.exp (X + 20)
        ≤ K0 * Real.exp (-(c0 / 16) * L) := by
      rw [hK0]
      nlinarith [hA, hB, hC]
    have hfin : Kp * (K0 * Real.exp (-(c0 / 16) * L)) = (Kp * K0) * z ^ (-(c0 / 16)) := by
      rw [hzrpow]; ring
    refine le_trans ?_ (le_of_eq hfin)
    exact mul_le_mul_of_nonneg_left hsum hKp.le

end Commons.Analysis.ExpLog