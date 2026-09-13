import Submission.Commons.Analysis.Calculus.Bounds.sqrt_quad_upper
import Submission.Commons.Analysis.Calculus.Bounds.sqrt_quad_final_bound

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Calculus.Bounds

theorem gradient_arith {s1 Z r C0 δ hh B X Yc qc App Wp : ℝ}
    (hs1 : 0 < s1) (hZ : 0 < Z) (hr : 0 < r) (hC0 : 1 ≤ C0)
    (hδeq : δ = 1 / (64 * C0 ^ 2))
    (hh1 : 2 * δ ≤ hh) (hh2 : hh ≤ 4 * δ * C0)
    (hB : B = s1 * qc - App)
    (hXnn : 0 ≤ X) (hX : X ≤ (3 / 2) * s1 * r ^ 2)
    (hqc : 0 < qc)
    (hcs : -(Real.sqrt B * Real.sqrt X) ≤ Yc)
    (hineq : 0 ≥ (2 * δ - 2 * hh ^ 2) * B + 8 * hh * Yc / Z - 6 * s1 / Z - 12 * X / Z ^ 2)
    (hL1 : App / qc + hh * qc - 2 * Wp / Z = 0)
    (hWp : Wp ≤ r * Real.sqrt qc)
    (hZr : Z ≤ r ^ 2) :
    Real.sqrt qc * Z ≤ 68 * C0 ^ 2 * r := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hhh_pos : 0 < hh := lt_of_lt_of_le (by linarith [hδpos]) hh1
  have hhh_le : hh ≤ 1/(16*C0) := by
    have he : 4 * δ * C0 = 1/(16*C0) := by rw [hδeq]; field_simp <;> ring
    rw [he] at hh2; exact hh2
  have hhh_sq_le : hh^2 ≤ 1/(256*C0^2) := by
    have h16 : (1/(16*C0))^2 = 1/(256*C0^2) := by field_simp <;> ring
    calc hh^2 ≤ (1/(16*C0))^2 := pow_le_pow_left₀ hhh_pos.le hhh_le 2
       _ = 1/(256*C0^2) := h16
  have hc_ub : 2*δ - 2*hh^2 ≤ 1/(32*C0^2) := by
    have he : 2*δ = 1/(32*C0^2) := by rw [hδeq]; field_simp <;> ring
    nlinarith [he, sq_nonneg hh]
  have hc_lb : 3/(128*C0^2) ≤ 2*δ - 2*hh^2 := by
    have hkey : 2*(1/(64*C0^2)) - 2*(1/(256*C0^2)) = 3/(128*C0^2) := by field_simp <;> ring
    have hd : 2*δ = 2*(1/(64*C0^2)) := by rw [hδeq]
    nlinarith [hhh_sq_le, hkey, hd]
  have hc_pos : 0 < 2*δ - 2*hh^2 := by
    have h3 : (0:ℝ) < 3/(128*C0^2) := by positivity
    linarith [hc_lb]
  have hsum : hh^2 + (2*δ - 2*hh^2) ≤ 9/(256*C0^2) := by
    have hd : 2*δ = 2*(1/(64*C0^2)) := by rw [hδeq]
    have hkey : 2*(1/(64*C0^2)) = 8/(256*C0^2) := by field_simp <;> ring
    have h9 : (8:ℝ)/(256*C0^2) ≤ 9/(256*C0^2) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    nlinarith [hd, hkey, h9, sq_nonneg hh]
  by_contra hgoal
  push_neg at hgoal
  set v := Real.sqrt qc with hvdef
  have hv_pos : 0 < v := by rw [hvdef]; exact Real.sqrt_pos.2 hqc
  have hv_sq : v^2 = qc := by rw [hvdef, Real.sq_sqrt hqc.le]
  have hv_gt : 68*C0^2*r/Z < v := by
    rw [div_lt_iff₀ hZ]; linarith [hgoal]
  have h2d : 2*δ = 1/(32*C0^2) := by rw [hδeq]; field_simp <;> ring
  have hhlt : 2*r/Z < hh*v := by
    have step1 : (2*δ)*v ≤ hh*v := mul_le_mul_of_nonneg_right hh1 hv_pos.le
    have hpos : (0:ℝ) < 1/(32*C0^2) := by positivity
    have hmul := mul_lt_mul_of_pos_left hv_gt hpos
    have heq : (1/(32*C0^2)) * (68*C0^2*r/Z) = 68*r/(32*Z) := by field_simp
    rw [heq] at hmul
    have h17 : 2*r/Z < 68*r/(32*Z) := by
      rw [div_lt_div_iff₀ hZ (by positivity : (0:ℝ) < 32*Z)]; nlinarith [hr, hZ]
    have step2 : 2*r/Z < (2*δ)*v := by rw [h2d]; linarith [hmul, h17]
    linarith [step1, step2]
  have hBform : B = qc * (s1 + hh*qc - 2*Wp/Z) := by
    have h1 : App/qc = 2*Wp/Z - hh*qc := by linarith [hL1]
    rw [div_eq_iff hqc.ne'] at h1
    rw [hB, h1]; ring
  have hWp' : Wp ≤ r*v := by rw [hvdef]; exact hWp
  have hhqc_gt : 2*Wp/Z < hh*qc := by
    have h1 : 2*Wp/Z ≤ 2*(r*v)/Z := by
      apply div_le_div_of_nonneg_right _ hZ.le
      nlinarith [hWp']
    have h2 : 2*(r*v)/Z < hh*qc := by
      have hq : hh*qc = hh*v^2 := by rw [← hv_sq]
      rw [hq]
      have hm := mul_lt_mul_of_pos_right hhlt hv_pos
      have he : (2*r/Z)*v = 2*(r*v)/Z := by ring
      rw [he] at hm; linarith [hm]
    linarith [h1, h2]
  have hBpos : 0 < B := by
    rw [hBform]
    apply mul_pos hqc
    linarith [hhqc_gt, hs1]
  have hB_ge : s1*qc ≤ B := by
    rw [hBform]
    have hbr : s1 ≤ s1 + hh*qc - 2*Wp/Z := by linarith [hhqc_gt]
    have hm := mul_le_mul_of_nonneg_left hbr hqc.le
    linarith [hm]
  have hsqB : Real.sqrt s1 * v ≤ Real.sqrt B := by
    have h1 : Real.sqrt (s1*qc) ≤ Real.sqrt B := Real.sqrt_le_sqrt hB_ge
    rw [Real.sqrt_mul hs1.le qc, ← hvdef] at h1
    exact h1
  have hP_ge : Real.sqrt s1 * v * Z ≤ Real.sqrt B * Z :=
    mul_le_mul_of_nonneg_right hsqB hZ.le
  have hquad : (2*δ - 2*hh^2) * (Real.sqrt B * Z)^2 ≤ 8*hh*Real.sqrt X*(Real.sqrt B*Z) + 6*s1*Z + 12*X := by
    have hBnn : 0 ≤ B := hBpos.le
    have hLZ : (2*δ - 2*hh^2)*B + 8*hh*Yc/Z - 6*s1/Z - 12*X/Z^2 ≤ 0 := hineq
    have hZ2 : (0:ℝ) < Z^2 := by positivity
    have hmm := mul_le_mul_of_nonneg_right hLZ hZ2.le
    have hsimp : ((2*δ - 2*hh^2)*B + 8*hh*Yc/Z - 6*s1/Z - 12*X/Z^2)*Z^2
        = (2*δ - 2*hh^2)*B*Z^2 + 8*hh*Yc*Z - 6*s1*Z - 12*X := by
      field_simp <;> ring
    rw [hsimp, zero_mul] at hmm
    have hA : -8*hh*Yc*Z ≤ 8*hh*Real.sqrt B*Real.sqrt X*Z := by
      have h1 : -Yc ≤ Real.sqrt B * Real.sqrt X := by linarith [hcs]
      have h2 : (8*hh*Z) * (-Yc) ≤ (8*hh*Z) * (Real.sqrt B * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith [h2]
    have hstep : (2*δ - 2*hh^2)*B*Z^2 ≤ 8*hh*Real.sqrt B*Real.sqrt X*Z + 6*s1*Z + 12*X := by
      linarith [hmm, hA]
    have hBZ2 : B*Z^2 = (Real.sqrt B*Z)^2 := by rw [mul_pow, Real.sq_sqrt hBnn]
    have hr1 : 8*hh*Real.sqrt X*(Real.sqrt B*Z) = 8*hh*Real.sqrt B*Real.sqrt X*Z := by ring
    nlinarith [hstep, hBZ2, hr1]
  have hquad' : (2*δ - 2*hh^2) * (Real.sqrt B*Z)^2 - 2*(4*hh*Real.sqrt X)*(Real.sqrt B*Z) ≤ 6*s1*Z+12*X := by
    nlinarith [hquad]
  have hP_nn : 0 ≤ Real.sqrt B * Z := by positivity
  have hb_nn : 0 ≤ 4*hh*Real.sqrt X := by positivity
  have hQ_nn : 0 ≤ 6*s1*Z + 12*X := by positivity
  have hT := sqrt_quad_upper hc_pos hb_nn hP_nn hQ_nn hquad'
  have hTb := sqrt_quad_final_bound hs1 hr hC0 hhh_pos hhh_le hc_lb hc_pos hsum hXnn hX hZ hZr
  have hP_le : Real.sqrt B * Z ≤ 68*C0^2*Real.sqrt s1*r := le_trans hT hTb
  have hs1root : 0 < Real.sqrt s1 := Real.sqrt_pos.2 hs1
  have hthis : Real.sqrt s1 * v * Z ≤ 68*C0^2*Real.sqrt s1*r := le_trans hP_ge hP_le
  have hvZ_le : v*Z ≤ 68*C0^2*r := by
    have h1 : Real.sqrt s1 * (v*Z) ≤ Real.sqrt s1 * (68*C0^2*r) := by
      calc Real.sqrt s1 * (v*Z) = Real.sqrt s1 * v * Z := by ring
        _ ≤ 68*C0^2*Real.sqrt s1*r := hthis
        _ = Real.sqrt s1 * (68*C0^2*r) := by ring
    exact (mul_le_mul_iff_of_pos_left hs1root).mp h1
  rw [hvdef] at hvZ_le
  linarith [hvZ_le, hgoal]

end Commons.Analysis.Calculus.Bounds
