import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Submission.Commons.Analysis.ExpLog.log4_le_140

open Real

namespace Commons.Analysis.SpecialFunctions.Gamma

private lemma log_ge_one_sub_inv {y : ℝ} (hy : 0 < y) : 1 - y⁻¹ ≤ Real.log y := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h
  linarith

private lemma log4_mul_sub_le_log {x : ℝ} (hx1 : (1:ℝ)/2 ≤ x) (hx2 : x ≤ 1) :
    Real.log 4 * (x - 1) ≤ Real.log x := by
  have hconc : ConcaveOn ℝ (Set.Ioi (0:ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have h2 : (1/2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have ha : (0:ℝ) ≤ 2*x - 1 := by linarith
  have hb : (0:ℝ) ≤ 2*(1 - x) := by linarith
  have hab : 2*x - 1 + 2*(1 - x) = 1 := by ring
  have key := hconc.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at key
  have hloghalf : Real.log (1/2) = - Real.log 2 := by
    rw [show (1:ℝ)/2 = 2⁻¹ by norm_num, Real.log_inv]
  have harg : (2*x - 1) * 1 + 2 * (1 - x) * (1/2) = x := by ring
  rw [harg, hloghalf] at key
  rw [Real.log_four_eq]
  nlinarith [key]

private lemma poly_aux (u v : ℝ) (hu1 : (1:ℝ)/2 ≤ u) (hu2 : u ≤ 8) (hv : 0 ≤ v)
    (hc : 0 ≤ u^2 - 16 - 16*v - 3*v^2) :
    6*u*(2*v^2+u)*(u^2 - 16 - 16*v - 3*v^2) ≤ (u^2+v^2)*(6*u^2-2*v^2-u) := by
  have hu0 : 0 ≤ u := by linarith
  have hu2sq : u^2 ≤ 64 := by nlinarith
  have hB0 : 0 ≤ 12*(u^2-16-16*v-3*v^2)*v^2 + (u^2-16-16*v-3*v^2) + 4*v^2+16*v+16 := by
    nlinarith [sq_nonneg v, sq_nonneg u, hc]
  have hE : 0 ≤ (22*(u^2-16-16*v-3*v^2)*v^2
          + 96*(u^2-16-16*v-3*v^2)*v
          + 96*(u^2-16-16*v-3*v^2)
          + 64*v^4 + 640*v^3 + 2176*v^2 + 3072*v + 1536)
        - 8*(12*(u^2-16-16*v-3*v^2)*v^2
          + (u^2-16-16*v-3*v^2) + 4*v^2 + 16*v + 16) := by
    have hv2 : v^2 ≤ 16 := by nlinarith
    nlinarith [sq_nonneg v, sq_nonneg (v-1), sq_nonneg (u-8)]
  have key : (u^2+v^2)*(6*u^2-2*v^2-u) - 6*u*(2*v^2+u)*(u^2 - 16 - 16*v - 3*v^2)
      = (22*(u^2-16-16*v-3*v^2)*v^2
          + 96*(u^2-16-16*v-3*v^2)*v
          + 96*(u^2-16-16*v-3*v^2)
          + 64*v^4 + 640*v^3 + 2176*v^2 + 3072*v + 1536)
        - u*(12*(u^2-16-16*v-3*v^2)*v^2
          + (u^2-16-16*v-3*v^2) + 4*v^2 + 16*v + 16) := by
    ring
  nlinarith [key, hE, hB0, hu2]

theorem stirling_shift_aux (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) (hu2 : u ≤ 8) (hv : 0 ≤ v) :
    0 ≤ Real.log ((4 + 2 * v) / Real.sqrt (u ^ 2 + v ^ 2)) + u / (2 * v ^ 2 + u) -
      1 / (6 * u) := by
  have hu0 : 0 < u := by linarith
  have hS2pos : 0 < u^2 + v^2 := by nlinarith [sq_nonneg v, hu1]
  set S : ℝ := Real.sqrt (u^2 + v^2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.mpr hS2pos
  have hSsq : S^2 = u^2 + v^2 := by rw [hSdef]; exact Real.sq_sqrt (le_of_lt hS2pos)
  have hApos : 0 < 4 + 2*v := by linarith
  have hden : 0 < 2*v^2 + u := by nlinarith [sq_nonneg v, hu0]
  have h6u : 0 < 6*u := by linarith
  have hSle2A : S ≤ 2*(4+2*v) := by
    rw [hSdef]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [hu1, hu2, hv, sq_nonneg v]⟩
  have hxhalf : (1:ℝ)/2 ≤ (4+2*v)/S := by
    rw [le_div_iff₀ hSpos]
    linarith
  have hxpos : 0 < (4+2*v)/S := by
    apply div_pos hApos hSpos
  rcases le_total (1:ℝ) ((4+2*v)/S) with hge | hle
  · have hSleA : S ≤ 4+2*v := (one_le_div hSpos).mp hge
    have hlogx : 1 - ((4+2*v)/S)⁻¹ ≤ Real.log ((4+2*v)/S) := log_ge_one_sub_inv hxpos
    rw [inv_div] at hlogx
    have hsubnn : 0 ≤ 1 - S/(4+2*v) := by
      rw [sub_nonneg, div_le_one hApos]; exact hSleA
    rcases le_or_gt (2*v^2+u) (6*u^2) with ha | hb
    · have hGnn : 0 ≤ u/(2*v^2+u) - 1/(6*u) := by
        rw [sub_nonneg, div_le_div_iff₀ h6u hden]
        nlinarith [ha]
      linarith [hlogx, hsubnn, hGnn]
    · have h9 : (3*S)^2 < (2*(4+2*v))^2 := by
        have h : 9*S^2 < 4*(4+2*v)^2 := by
          rw [hSsq]; nlinarith [hb, hu1, hu2, hv, sq_nonneg v]
        nlinarith [h]
      have h3Snn : 0 ≤ 3*S := by linarith [hSpos]
      have h2Ann : 0 ≤ 2*(4+2*v) := by linarith [hApos]
      have hlt : 3*S < 2*(4+2*v) := by
        have h := (sq_lt_sq.mp h9)
        rwa [abs_of_nonneg h3Snn, abs_of_nonneg h2Ann] at h
      have hsub_gt : 1/3 < 1 - S/(4+2*v) := by
        have h' : S/(4+2*v) < 2/3 := by
          rw [div_lt_iff₀ hApos]; linarith [hlt]
        linarith
      have hGge : -(1/3) ≤ u/(2*v^2+u) - 1/(6*u) := by
        have h1 : 0 ≤ u/(2*v^2+u) := div_nonneg (le_of_lt hu0) (le_of_lt hden)
        have h2 : 1/(6*u) ≤ 1/3 := by
          rw [div_le_iff₀ h6u]; nlinarith [hu1]
        linarith
      linarith [hlogx, hsub_gt, hGge]
  · have hAleS : 4+2*v ≤ S := (div_le_one hSpos).mp hle
    have hlogx : Real.log 4 * ((4+2*v)/S - 1) ≤ Real.log ((4+2*v)/S) :=
      log4_mul_sub_le_log hxhalf hle
    have hlogx' : -Real.log 4 * (1 - (4+2*v)/S) ≤ Real.log ((4+2*v)/S) := by
      have heq : (4+2*v)/S - 1 = -(1 - (4+2*v)/S) := by ring
      rw [heq] at hlogx
      linarith [hlogx]
    have hc : 0 ≤ u^2 - 16 - 16*v - 3*v^2 := by
      have hs : (4+2*v)^2 ≤ S^2 := by nlinarith [hAleS, hSpos]
      nlinarith [hs, hSsq]
    have hpoly := poly_aux u v hu1 hu2 hv hc
    have hlog4le : Real.log 4 ≤ (3:ℝ)/2 := by
      have := Commons.Analysis.ExpLog.log4_le_140
      linarith
    -- key: log 4 * (1 - A/S) ≤ G
    have hRnn : 0 ≤ 1 - (4+2*v)/S := by
      rw [sub_nonneg, div_le_one hSpos]; exact hAleS
    have hRle : 1 - (4+2*v)/S ≤ 2*(u^2 - 16 - 16*v - 3*v^2)/(3*S^2) := by
      have hReq : 1 - (4+2*v)/S = (u^2 - 16 - 16*v - 3*v^2)/(S*(S+(4+2*v))) := by
        have hSa : S + (4+2*v) ≠ 0 := by positivity
        have hSne : S ≠ 0 := ne_of_gt hSpos
        field_simp
        nlinarith [hSsq]
      rw [hReq]
      have hdenge : (3:ℝ)/2 * S^2 ≤ S*(S + (4+2*v)) := by
        have hAge : S/2 ≤ 4+2*v := by
          have := (le_div_iff₀ hSpos).mp hxhalf
          linarith
        nlinarith [hAge, hSpos]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hprod : 0 ≤ (u^2-16-16*v-3*v^2) * (S*(S+(4+2*v)) - (3/2)*S^2) :=
        mul_nonneg hc (by linarith [hdenge])
      nlinarith [hprod]
    have hkey : Real.log 4 * (1 - (4+2*v)/S) ≤ u/(2*v^2+u) - 1/(6*u) := by
      have hstep1 : Real.log 4 * (1 - (4+2*v)/S) ≤ Real.log 4 * (2*(u^2 - 16 - 16*v - 3*v^2)/(3*S^2)) := by
        apply mul_le_mul_of_nonneg_left hRle
        exact le_of_lt (Real.log_pos (by norm_num))
      have hstep2 : Real.log 4 * (2*(u^2 - 16 - 16*v - 3*v^2)/(3*S^2)) ≤ (u^2 - 16 - 16*v - 3*v^2)/S^2 := by
        have hS2 : 0 < S^2 := by positivity
        have hcs : 0 ≤ (u^2 - 16 - 16*v - 3*v^2)/S^2 := div_nonneg hc (le_of_lt hS2)
        have hcoef : 2*Real.log 4/3 ≤ 1 := by linarith [hlog4le]
        have heq : Real.log 4 * (2*(u^2 - 16 - 16*v - 3*v^2)/(3*S^2))
            = (2*Real.log 4/3)*((u^2 - 16 - 16*v - 3*v^2)/S^2) := by
          field_simp
        rw [heq]
        calc (2*Real.log 4/3)*((u^2 - 16 - 16*v - 3*v^2)/S^2)
              ≤ 1*((u^2 - 16 - 16*v - 3*v^2)/S^2) := mul_le_mul_of_nonneg_right hcoef hcs
          _ = (u^2 - 16 - 16*v - 3*v^2)/S^2 := by ring
      have hstep3 : (u^2 - 16 - 16*v - 3*v^2)/S^2 ≤ u/(2*v^2+u) - 1/(6*u) := by
        have hGexpr : u/(2*v^2+u) - 1/(6*u) = (6*u^2-2*v^2-u)/(6*u*(2*v^2+u)) := by
          field_simp
          ring
        rw [hGexpr, hSsq]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hpoly]
      linarith [hstep1, hstep2, hstep3]
    linarith [hlogx', hkey]

end Commons.Analysis.SpecialFunctions.Gamma