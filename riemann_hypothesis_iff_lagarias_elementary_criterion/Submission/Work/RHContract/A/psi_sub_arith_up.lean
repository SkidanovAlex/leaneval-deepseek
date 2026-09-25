import Mathlib

set_option maxHeartbeats 2000000

namespace Work.RHContract.A

/-- `(x^{1/4})^2 = x^{1/2}` for `x ≥ 0`. -/
lemma q_pow2 (x : ℝ) (hx : 0 ≤ x) : (x^(1/4:ℝ))^2 = x^(1/2:ℝ) := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 2, ← Real.rpow_mul hx]; norm_num

/-- `(x^{1/4})^3 = x^{3/4}` for `x ≥ 0`. -/
lemma q_pow3 (x : ℝ) (hx : 0 ≤ x) : (x^(1/4:ℝ))^3 = x^(3/4:ℝ) := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 3, ← Real.rpow_mul hx]; norm_num

/-- `(x^{1/4})^4 = x` for `x ≥ 0`. -/
lemma q_pow4 (x : ℝ) (hx : 0 ≤ x) : (x^(1/4:ℝ))^4 = x := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 4, ← Real.rpow_mul hx]; norm_num

/-- `(x^{1/4})^6 = x^{3/2}` for `x ≥ 0`. -/
lemma q_pow6 (x : ℝ) (hx : 0 ≤ x) : (x^(1/4:ℝ))^6 = x^(3/2:ℝ) := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 6, ← Real.rpow_mul hx]; norm_num

/-- Taylor bound: `(1+u)^{3/2} ≤ 1 + (3/2)u + (3/8)u^2` for `u ≥ 0`. -/
lemma taylor32 (u : ℝ) (hu : 0 ≤ u) :
    (1 + u)^(3/2:ℝ) ≤ 1 + 3/2*u + 3/8*u^2 := by
  set A : ℝ := 1 + 3/2*u + 3/8*u^2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; nlinarith [sq_nonneg u, hu]
  have h1u : 0 ≤ 1 + u := by linarith
  have hpn : 0 ≤ (1+u)^(3/2:ℝ) := Real.rpow_nonneg h1u _
  have hpow : ((1+u)^(3/2:ℝ))^2 = (1+u)^3 := by
    rw [← Real.rpow_natCast ((1+u)^(3/2:ℝ)) 2, ← Real.rpow_natCast (1+u) 3, ← Real.rpow_mul h1u]
    norm_num
  have hkey : (1+u)^3 ≤ A^2 := by rw [hA]; nlinarith [hu, sq_nonneg u, pow_nonneg hu 3]
  have h2 : ((1+u)^(3/2:ℝ))^2 ≤ A^2 := by rw [hpow]; exact hkey
  have h3 := sq_le_sq.mp h2
  rwa [abs_of_nonneg hpn, abs_of_nonneg hA0] at h3

/-- For `v > 0` and `c ≥ 0`, `(v³(v+c))^{3/2} ≤ v⁶ + (3/2)c v⁵ + (3/8)c² v⁴`. -/
lemma key_bound (v c : ℝ) (hv : 0 < v) (hc : 0 ≤ c) :
    (v^3*(v+c))^(3/2:ℝ) ≤ v^6 + 3/2*c*v^5 + 3/8*c^2*v^4 := by
  have hv0 : 0 ≤ v := le_of_lt hv
  have hvc : 0 ≤ v + c := by linarith
  have hsub : v^(1/2:ℝ) * (v+c)^(3/2:ℝ) ≤ v^2 + 3/2*c*v + 3/8*c^2 := by
    have hsq : (v^(1/2:ℝ) * (v+c)^(3/2:ℝ))^2 = v*(v+c)^3 := by
      rw [mul_pow]
      rw [← Real.rpow_natCast (v^(1/2:ℝ)) 2, ← Real.rpow_mul hv0]
      rw [← Real.rpow_natCast ((v+c)^(3/2:ℝ)) 2, ← Real.rpow_mul hvc]
      norm_num
    have hkey : v*(v+c)^3 ≤ (v^2 + 3/2*c*v + 3/8*c^2)^2 := by
      have hid : (v^2 + 3/2*c*v + 3/8*c^2)^2 - v*(v+c)^3 = c^3*v/8 + 9*c^4/64 := by ring
      have hnn : 0 ≤ c^3*v/8 + 9*c^4/64 := by positivity
      linarith [hid]
    have h2 : (v^(1/2:ℝ)*(v+c)^(3/2:ℝ))^2 ≤ (v^2+3/2*c*v+3/8*c^2)^2 := by rw [hsq]; exact hkey
    have hA0 : 0 ≤ v^2+3/2*c*v+3/8*c^2 := by positivity
    have hp0 : 0 ≤ v^(1/2:ℝ)*(v+c)^(3/2:ℝ) := by positivity
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg hp0, abs_of_nonneg hA0] at h3
  have e1 : (v^3*(v+c))^(3/2:ℝ) = v^(9/2:ℝ) * (v+c)^(3/2:ℝ) := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ v^3) hvc]
    congr 1
    rw [← Real.rpow_natCast v 3, ← Real.rpow_mul hv0]
    norm_num
  have e2 : v^(9/2:ℝ) = v^4 * v^(1/2:ℝ) := by
    rw [← Real.rpow_natCast v 4, ← Real.rpow_add hv]
    norm_num
  calc (v^3*(v+c))^(3/2:ℝ)
      = v^(9/2:ℝ)*(v+c)^(3/2:ℝ) := e1
    _ = v^4 * (v^(1/2:ℝ)*(v+c)^(3/2:ℝ)) := by rw [e2]; ring
    _ ≤ v^4 * (v^2+3/2*c*v+3/8*c^2) := by apply mul_le_mul_of_nonneg_left hsub; positivity
    _ = v^6 + 3/2*c*v^5 + 3/8*c^2*v^4 := by ring

/-- The univariate polynomial inequality `(9/125)v² + (774/100000)v + 1/10 ≤ (101/8600)v³ + 2`
for `v ≥ 0`. -/
lemma poly_step (v : ℝ) (hv : 0 ≤ v) : 9/125*v^2 + 774/100000*v + 1/10 ≤ 101/8600*v^3 + 2 := by
  have h1 : 9/125*v^2 ≤ 2/25*v^2 := by nlinarith [sq_nonneg v]
  have h2 : 774/100000*v ≤ 1/100*v := by nlinarith [hv]
  have h3 : (1/100:ℝ)*v^3 ≤ 101/8600*v^3 := by nlinarith [pow_nonneg hv 3]
  have hmain : (2/25:ℝ)*v^2 + 1/100*v + 1/10 ≤ 1/100*v^3 + 2 := by
    have hkey : (0:ℝ) ≤ v*(v-5)^2 + 2*(v-13/2)^2 + 211/2 := by positivity
    have hid : v*(v-5)^2 + 2*(v-13/2)^2 + 211/2 = v^3 - 8*v^2 - v + 190 := by ring
    have h4 : (0:ℝ) ≤ v^3 - 8*v^2 - v + 190 := by linarith [hkey, hid]
    linarith [h4]
  linarith [h1, h2, h3, hmain]

-- Pure real arithmetic (Mathlib only). With h := (43/100)·x^{3/4}, β ≤ 48/1000 and x ≥ 200 this is the
-- upper estimate for ψ(x) − x coming from the averaged explicit formula.
theorem psi_sub_arith_up (β x : ℝ) (hβ : β ≤ 48/1000) (hx : 200 ≤ x) :
    (43/100 * x ^ (3/4 : ℝ))/2 - Real.log (2 * Real.pi)
      + (β * ((x + 43/100 * x ^ (3/4 : ℝ)) ^ (3/2 : ℝ) + x ^ (3/2 : ℝ))
          + 2 * Real.log 2 / x) / (43/100 * x ^ (3/4 : ℝ))
      ≤ 0.45 * x ^ (3/4 : ℝ) + 2 := by
  have hx0 : (0:ℝ) < x := by linarith
  have hx0' : (0:ℝ) ≤ x := le_of_lt hx0
  set c : ℝ := 43/100 with hc
  set t : ℝ := x ^ (3/4:ℝ) with ht
  set v : ℝ := x ^ (1/4:ℝ) with hv
  have hc0 : (0:ℝ) < c := by rw [hc]; norm_num
  have hc0' : (0:ℝ) ≤ c := le_of_lt hc0
  have ht0 : (0:ℝ) < t := by rw [ht]; exact Real.rpow_pos_of_pos hx0 _
  have hv0 : (0:ℝ) < v := by rw [hv]; exact Real.rpow_pos_of_pos hx0 _
  have hv0' : (0:ℝ) ≤ v := le_of_lt hv0
  have hx_v4 : x = v^4 := by rw [hv]; exact (q_pow4 x hx0').symm
  have ht_v3 : t = v^3 := by rw [ht, hv]; exact (q_pow3 x hx0').symm
  have hhalf_v2 : x^(1/2:ℝ) = v^2 := by rw [hv]; exact (q_pow2 x hx0').symm
  have hquart_v : x^(1/4:ℝ) = v := by rw [hv]
  have hlog2pi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hct_nn : 0 ≤ c*t := mul_nonneg hc0' (le_of_lt ht0)
  have hxct_nn : 0 ≤ x + c*t := by linarith
  have hSnn : 0 ≤ (x+c*t)^(3/2:ℝ) + x^(3/2:ℝ) :=
    add_nonneg (Real.rpow_nonneg hxct_nn _) (Real.rpow_nonneg hx0' _)
  have hN : β * ((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2*Real.log 2/x
        ≤ (48/1000)*((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2/x := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hβ hSnn
    · have h2l : 2*Real.log 2 ≤ 2 := by linarith
      exact div_le_div_of_nonneg_right h2l hx0'
  have hNdiv : (β * ((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2*Real.log 2/x)/(c*t)
        ≤ ((48/1000)*((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2/x)/(c*t) :=
    div_le_div_of_nonneg_right hN hct_nn
  have key2 : (x + c*t)^(3/2:ℝ) ≤ v^6 + 3/2*c*v^5 + 3/8*c^2*v^4 := by
    rw [show x + c*t = v^3*(v+c) by rw [hx_v4, ht_v3]; ring]
    exact key_bound v c hv0 hc0'
  have hstep1 : (x+c*t)^(3/2:ℝ)/(c*t) ≤ (v^6+3/2*c*v^5+3/8*c^2*v^4)/(c*t) :=
    div_le_div_of_nonneg_right key2 hct_nn
  have hstep2 : (v^6+3/2*c*v^5+3/8*c^2*v^4)/(c*t) = t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ) := by
    rw [ht_v3, hhalf_v2, hquart_v]; field_simp
  have hA : (x+c*t)^(3/2:ℝ)/(c*t) ≤ t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ) :=
    le_trans hstep1 (le_of_eq hstep2)
  have hx32_t : x^(3/2:ℝ) = t^2 := by
    rw [show (3/2:ℝ) = (3/4)+(3/4) by norm_num, Real.rpow_add hx0, ← ht]; ring
  have hB : x^(3/2:ℝ)/(c*t) = t/c := by
    rw [hx32_t]; field_simp
  have hSD : ((x+c*t)^(3/2:ℝ) + x^(3/2:ℝ))/(c*t) ≤ 2*t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ) := by
    calc ((x+c*t)^(3/2:ℝ) + x^(3/2:ℝ))/(c*t)
        = (x+c*t)^(3/2:ℝ)/(c*t) + x^(3/2:ℝ)/(c*t) := by rw [add_div]
      _ ≤ (t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ)) + t/c := add_le_add hA (le_of_eq hB)
      _ = 2*t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ) := by ring
  have hbig : ((48/1000)*((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2/x)/(c*t)
        ≤ 48/215*t + 9/125*x^(1/2:ℝ) + 774/100000*x^(1/4:ℝ) + 1/10 := by
    have hsplit : ((48/1000)*((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2/x)/(c*t)
        = (48/1000)*(((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ))/(c*t)) + (2/x)/(c*t) := by ring
    rw [hsplit]
    have h1 : (48/1000)*(((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ))/(c*t)) ≤ (48/1000)*(2*t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_left hSD (by norm_num)
    have h2 : (2/x)/(c*t) ≤ 1/10 := by
      rw [div_div]
      have hxcnn : 0 ≤ x*c := le_of_lt (mul_pos hx0 hc0)
      have ht1 : 1 ≤ t := by
        rw [ht]
        calc (1:ℝ) = 1^(3/4:ℝ) := (Real.one_rpow _).symm
          _ ≤ x^(3/4:ℝ) := Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
      have hml : x*c*1 ≤ x*c*t := mul_le_mul_of_nonneg_left ht1 hxcnn
      have hxc20 : (20:ℝ) ≤ x*c := by
        have := mul_le_mul_of_nonneg_right hx hc0'
        have : (20:ℝ) ≤ 200*c := by rw [hc]; norm_num
        linarith
      have hge : (20:ℝ) ≤ x*(c*t) := by nlinarith [hml, hxc20]
      have hdiv := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) < 20 by norm_num) hge
      linarith [hdiv]
    have harith : (48/1000)*(2*t/c + 3/2*x^(1/2:ℝ) + 3/8*c*x^(1/4:ℝ)) = 48/215*t + 9/125*x^(1/2:ℝ) + 774/100000*x^(1/4:ℝ) := by
      rw [hc]; field_simp; ring
    linarith [h1, h2, harith]
  have hBnd : (β * ((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2*Real.log 2/x)/(c*t)
        ≤ 48/215*t + 9/125*x^(1/2:ℝ) + 774/100000*x^(1/4:ℝ) + 1/10 :=
    le_trans hNdiv hbig
  have h_upper : (c*t)/2 - Real.log (2*Real.pi) + (β * ((x+c*t)^(3/2:ℝ)+x^(3/2:ℝ)) + 2*Real.log 2/x)/(c*t)
        ≤ (c*t)/2 + 48/215*t + 9/125*x^(1/2:ℝ) + 774/100000*x^(1/4:ℝ) + 1/10 := by
    linarith [hlog2pi, hBnd]
  have h_final : (c*t)/2 + 48/215*t + 9/125*x^(1/2:ℝ) + 774/100000*x^(1/4:ℝ) + 1/10 ≤ 0.45*t + 2 := by
    have hp := poly_step v hv0'
    rw [hc, ht_v3, hhalf_v2, hquart_v, show (0.45:ℝ) = 9/20 by norm_num]
    linarith [hp]
  linarith [h_upper, h_final]

end Work.RHContract.A
