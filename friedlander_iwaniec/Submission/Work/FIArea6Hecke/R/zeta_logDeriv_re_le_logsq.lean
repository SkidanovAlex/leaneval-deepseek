import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_inv_le_logPow_zeroFree
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

namespace Work.FIArea6Hecke.R

open Complex Metric
open scoped Real Topology

noncomputable section

/-- **Norm bound for `ζ'/ζ` in the strip `1 < Re s ≤ 2`, away from the real axis.**

The zero-free region of `ζ` has width `≫ 1/log`, so the disk of radius `≍ 1/log` around any
point `s` of the strip is zero-free; the Borel–Carathéodory log-derivative estimate
(`logDeriv_zeroFree_ball_bound_analytic`) applied to it, with the polynomial growth
(`zeta_strip_polyGrowth`) as upper bound and the inverse bound (`zeta_inv_le_logPow_zeroFree`)
at the centre, gives `O(log²)`. -/
theorem zeta_logDeriv_norm_le_logsq_largeIm :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → 60 ≤ |t| →
      ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
  obtain ⟨c₀, C₀, hc₀0, hC₀0, hZFR, hLD⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨cinv, Cinv, hcinv0, hCinv0, hinv⟩ :=
    Commons.NumberTheory.Zeta.zeta_inv_le_logPow_zeroFree
  obtain ⟨Cg, hCg0, hgrowth⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  set cmin : ℝ := min (min c₀ cinv) 1 with hcmin
  have hcmin0 : 0 < cmin := by rw [hcmin]; positivity
  have hcminc₀ : cmin ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcmin1 : cmin ≤ 1 := min_le_right _ _
  set K1 : ℝ := Real.log 2 + Real.log (max Cg 1) + max 0 (Real.log Cinv) + 8 + Cinv with hK1
  have hK10 : 0 < K1 := by
    have h1 : 0 ≤ Real.log (max Cg 1) := Real.log_nonneg (le_max_right _ _)
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 ≤ max 0 (Real.log Cinv) := le_max_left _ _
    rw [hK1]; linarith
  refine ⟨16 * K1 / cmin, by positivity, ?_⟩
  intro σ t hσ1 hσ2 ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set L : ℝ := Real.log (|t| + 3) with hL
  have htabs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hL1 : 1 ≤ L := by
    rw [hL]
    have hx : Real.exp 1 ≤ |t| + 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|t| + 3) := Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  set r : ℝ := cmin / (4 * L) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrle : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    nlinarith [hcmin1, hL1]
  -- `log (|t| + 4) ≤ 2 L`
  have hlog4 : Real.log (|t| + 4) ≤ 2 * L := by
    have h4 : |t| + 4 ≤ (|t| + 3) ^ 2 := by nlinarith [htabs]
    have h5 : Real.log (|t| + 4) ≤ Real.log ((|t| + 3) ^ 2) :=
      Real.log_le_log (by linarith) h4
    have h6 : Real.log ((|t| + 3) ^ 2) = 2 * Real.log (|t| + 3) := by
      rw [Real.log_pow]; norm_num
    rw [h6] at h5
    rw [← hL] at h5
    exact h5
  -- component bounds for points of the ball
  have him_of_ball : ∀ w : ℂ, w ∈ Metric.ball s r → |w.im - t| < r := by
    intro w hw
    have hwlt : ‖w - s‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h1 := Complex.abs_im_le_norm (w - s)
    have h2 : (w - s).im = w.im - t := by simp [hs]
    rw [h2] at h1
    exact lt_of_le_of_lt h1 hwlt
  have hre_of_ball : ∀ w : ℂ, w ∈ Metric.ball s r → |w.re - σ| < r := by
    intro w hw
    have hwlt : ‖w - s‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h1 := Complex.abs_re_le_norm (w - s)
    have h2 : (w - s).re = w.re - σ := by simp [hs]
    rw [h2] at h1
    exact lt_of_le_of_lt h1 hwlt
  have him1_of_ball : ∀ w : ℂ, w ∈ Metric.ball s r → 1 ≤ |w.im| := by
    intro w hw
    have h3 : |t| - |w.im| ≤ |w.im - t| := by
      have := abs_sub_abs_le_abs_sub t w.im
      rwa [abs_sub_comm] at this
    have h4 := him_of_ball w hw
    linarith [h3, h4, ht, hrle]
  -- the ball is zero-free
  have hball_nz : ∀ w : ℂ, w ∈ Metric.ball s r → riemannZeta w ≠ 0 := by
    intro w hw
    have hre := hre_of_ball w hw
    have him1 := him1_of_ball w hw
    have hwimle : |w.im| ≤ |t| + r := by
      have h3 : |w.im| - |t| ≤ |w.im - t| := abs_sub_abs_le_abs_sub w.im t
      have h4 := him_of_ball w hw
      linarith
    have hlogw : Real.log (|w.im| + 3) ≤ 2 * L := by
      have h7 : |w.im| + 3 ≤ |t| + 4 := by linarith
      exact le_trans (Real.log_le_log (by linarith [him1]) h7) hlog4
    have hlogwpos : 0 < Real.log (|w.im| + 3) := Real.log_pos (by linarith [him1])
    have hrle' : r ≤ c₀ / Real.log (|w.im| + 3) := by
      have h1 : r * Real.log (|w.im| + 3) ≤ c₀ := by
        rw [hr]
        have h2 : cmin / (4 * L) * Real.log (|w.im| + 3) ≤ cmin / (4 * L) * (2 * L) :=
          mul_le_mul_of_nonneg_left hlogw (by positivity)
        have h3 : cmin / (4 * L) * (2 * L) = cmin / 2 := by
          field_simp; ring
        linarith [h2, h3.le, h3.ge, hcminc₀]
      rwa [le_div_iff₀ hlogwpos]
    have hreg : 1 - c₀ / Real.log (|w.im| + 3) ≤ w.re := by
      have h1 : σ - r < w.re := by
        have h2 : -(r) < w.re - σ := (abs_lt.mp hre).1
        linarith
      have h2 : 1 - r ≤ σ - r := by linarith
      linarith [h1, h2, hrle']
    have hz := hZFR w.im him1 w.re hreg
    rw [mul_comm Complex.I (w.im : ℂ)] at hz
    rwa [Complex.re_add_im] at hz
  -- growth on the ball
  have hball_growth : ∀ w : ℂ, w ∈ Metric.ball s r → ‖riemannZeta w‖ ≤ Cg * (|t| + 4) ^ 4 := by
    intro w hw
    have hre := hre_of_ball w hw
    have him1 := him1_of_ball w hw
    have hrelo : -1 ≤ w.re := by
      have h2 : -(r) < w.re - σ := (abs_lt.mp hre).1
      linarith [h2, hσ1, hrle]
    have hrehi : w.re ≤ 3 := by
      have h2 : w.re - σ < r := (abs_lt.mp hre).2
      linarith [h2, hσ2, hrle]
    have h1 := hgrowth w.re w.im hrelo hrehi him1
    rw [mul_comm Complex.I (w.im : ℂ)] at h1
    rw [Complex.re_add_im w] at h1
    have h2 : |w.im| + 3 ≤ |t| + 4 := by
      have h3 : |w.im| - |t| ≤ |w.im - t| := abs_sub_abs_le_abs_sub w.im t
      have h4 := him_of_ball w hw
      linarith
    have h3 : (|w.im| + 3) ^ 4 ≤ (|t| + 4) ^ 4 :=
      pow_le_pow_left₀ (by linarith [him1]) h2 4
    exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (le_of_lt hCg0))
  -- lower bound at the centre
  have hcenter : 1 / (Cinv * (Real.log (|t| + 2)) ^ Cinv) ≤ ‖riemannZeta s‖ := by
    have h3t : (3 : ℝ) ≤ |t| := by linarith
    have hlog2pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
    have hreg : 1 - cinv / Real.log (|t| + 2) ≤ σ := by
      have h4 : 0 < cinv / Real.log (|t| + 2) := div_pos hcinv0 hlog2pos
      linarith
    have h := hinv σ t h3t hreg hσ2
    have hspos : 0 < ‖riemannZeta s‖ := by
      refine norm_pos_iff.mpr ?_
      have hlog3pos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith)
      have hreg0 : 1 - c₀ / Real.log (|t| + 3) ≤ σ := by
        have h4 : 0 < c₀ / Real.log (|t| + 3) := div_pos hc₀0 hlog3pos
        linarith
      have hz := hZFR t (by linarith) σ hreg0
      rw [mul_comm Complex.I (t : ℂ)] at hz
      simpa [hs] using hz
    have h' := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / ‖riemannZeta s‖ by positivity) h
    have heq : 1 / (1 / ‖riemannZeta s‖) = ‖riemannZeta s‖ := by
      rw [one_div, one_div, inv_inv]
    rw [heq] at h'
    exact h'
  set M : ℝ := max (Cg * (|t| + 4) ^ 4) 1 with hM
  set m : ℝ := min 1 (1 / (Cinv * (Real.log (|t| + 2)) ^ Cinv)) with hm
  have hmpos : 0 < m := by
    rw [hm]
    refine lt_min one_pos ?_
    have h1 : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
    exact div_pos one_pos (mul_pos hCinv0 (Real.rpow_pos_of_pos h1 Cinv))
  have hMm : m ≤ M := by
    rw [hm, hM]
    exact le_trans (min_le_left _ _) (le_max_right _ _)
  have hMg : ∀ w : ℂ, w ∈ Metric.ball s r → ‖riemannZeta w‖ ≤ M := by
    intro w hw
    rw [hM]; exact le_max_of_le_left (hball_growth w hw)
  have hmg : m ≤ ‖riemannZeta s‖ := by
    rw [hm]; exact le_trans (min_le_right _ _) hcenter
  have han : AnalyticOnNhd ℂ riemannZeta (Metric.ball s r) := by
    rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
    intro w hw
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro hw1
    have him1 := him1_of_ball w hw
    rw [hw1] at him1
    simp only [Complex.one_im, abs_zero] at him1
    linarith
  have hρ : (0 : ℝ) < r / 2 := by positivity
  have hρR : r / 2 < r - ‖s - s‖ := by
    rw [sub_self, norm_zero]; linarith
  have hball := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
      (g := riemannZeta) (c := s) (R := r) (m := m) (M := M)
      hrpos hmpos hMm han hball_nz hMg hmg (Metric.mem_ball_self hrpos) (r / 2) hρ hρR
  have hsy : ‖s - s‖ = 0 := by simp
  rw [hsy] at hball
  have hb : ‖deriv riemannZeta s / riemannZeta s‖
      ≤ 4 * (Real.log (2 * M) - Real.log m) / r := by
    refine le_trans hball ?_
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hcalc : 2 * (Real.log (2 * M) - Real.log m) * (0 + r / 2) / ((r - 0 - r / 2) * (r / 2))
        = 4 * (Real.log (2 * M) - Real.log m) / r := by
      have h1 : (0 + r / 2) = r / 2 := by ring
      have h2 : (r - 0 - r / 2) = r / 2 := by ring
      rw [h1, h2]
      have hden : (r / 2) * (r / 2) ≠ 0 := by positivity
      rw [div_eq_div_iff hden hrne]
      ring
    rw [hcalc]
  -- arithmetic: `log (2M) - log m ≤ K1 * L`
  have hA : Real.log (2 * M) - Real.log m ≤ K1 * L := by
    have hMle : max (Cg * (|t| + 4) ^ 4) 1 ≤ max Cg 1 * (|t| + 4) ^ 4 := by
      apply max_le
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · have h1 : (1 : ℝ) ≤ (|t| + 4) ^ 4 := one_le_pow₀ (by linarith [htabs])
        have h2 : (1 : ℝ) ≤ max Cg 1 := le_max_right _ _
        nlinarith [h1, h2]
    have hmaxpowpos : 0 < max Cg 1 * (|t| + 4) ^ 4 := by positivity
    have hlog2M : Real.log (2 * M) ≤ Real.log 2 + Real.log (max Cg 1) + 8 * L := by
      have h1 : Real.log (2 * M) ≤ Real.log (2 * (max Cg 1 * (|t| + 4) ^ 4)) :=
        Real.log_le_log (by positivity) (by rw [hM]; linarith)
      have h2 : Real.log (2 * (max Cg 1 * (|t| + 4) ^ 4))
          = Real.log 2 + Real.log (max Cg 1) + 4 * Real.log (|t| + 4) := by
        rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        have h3 : Real.log ((|t| + 4) ^ 4) = 4 * Real.log (|t| + 4) := by
          rw [Real.log_pow]; norm_num
        rw [h3]; ring
      have h4 : 4 * Real.log (|t| + 4) ≤ 8 * L := by linarith [hlog4]
      linarith
    have hlogm : -Real.log m ≤ max 0 (Real.log Cinv) + Cinv * L := by
      by_cases hy : (1 : ℝ) ≤ 1 / (Cinv * (Real.log (|t| + 2)) ^ Cinv)
      · have hm1 : m = 1 := by rw [hm]; exact min_eq_left hy
        rw [hm1, Real.log_one, neg_zero]
        have h1 : 0 ≤ max 0 (Real.log Cinv) := le_max_left _ _
        have h2 : 0 ≤ Cinv * L := by positivity
        linarith
      · have hy' : 1 / (Cinv * (Real.log (|t| + 2)) ^ Cinv) ≤ 1 := le_of_lt (lt_of_not_ge hy)
        have hm1 : m = 1 / (Cinv * (Real.log (|t| + 2)) ^ Cinv) := by
          rw [hm]; exact min_eq_right hy'
        rw [hm1, one_div, Real.log_inv, neg_neg]
        have h1 : Real.log (Cinv * (Real.log (|t| + 2)) ^ Cinv)
            = Real.log Cinv + Cinv * Real.log (Real.log (|t| + 2)) := by
          rw [Real.log_mul (ne_of_gt hCinv0)
            (ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) Cinv)),
            Real.log_rpow (Real.log_pos (by linarith))]
        rw [h1]
        have h2 : Real.log (Real.log (|t| + 2)) ≤ L := by
          have h3 : (0 : ℝ) < Real.log (|t| + 2) := Real.log_pos (by linarith)
          have h4 : Real.log (|t| + 2) ≤ |t| + 3 := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |t| + 2 by linarith)
            linarith
          have h5 : Real.log (Real.log (|t| + 2)) ≤ Real.log (|t| + 3) :=
            Real.log_le_log h3 h4
          rwa [hL]
        have h5 : Real.log Cinv ≤ max 0 (Real.log Cinv) := le_max_right _ _
        have h6 : Cinv * Real.log (Real.log (|t| + 2)) ≤ Cinv * L :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hCinv0)
        linarith
    have hbr : 0 ≤ Real.log 2 + Real.log (max Cg 1) + max 0 (Real.log Cinv) := by
      have h1 : 0 ≤ Real.log (max Cg 1) := Real.log_nonneg (le_max_right _ _)
      have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h3 : 0 ≤ max 0 (Real.log Cinv) := le_max_left _ _
      linarith
    have h5 : Real.log 2 + Real.log (max Cg 1) + max 0 (Real.log Cinv)
        ≤ (Real.log 2 + Real.log (max Cg 1) + max 0 (Real.log Cinv)) * L :=
      le_mul_of_one_le_right hbr hL1
    rw [hK1]
    linarith
  have hb2 : ‖deriv riemannZeta s / riemannZeta s‖ ≤ 16 * K1 / cmin * L ^ 2 := by
    refine le_trans hb ?_
    have h1 : 4 * (Real.log (2 * M) - Real.log m) / r
        = 16 * (Real.log (2 * M) - Real.log m) * L / cmin := by
      rw [hr]; field_simp; ring
    rw [h1]
    have h2 : 16 * (Real.log (2 * M) - Real.log m) * L / cmin ≤ 16 * (K1 * L) * L / cmin := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hcmin0)
      nlinarith [hA, hLpos]
    have h3 : 16 * (K1 * L) * L / cmin = 16 * K1 / cmin * L ^ 2 := by ring
    linarith [h2, h3.le, h3.ge]
  calc ‖deriv riemannZeta s / riemannZeta s‖ ≤ 16 * K1 / cmin * L ^ 2 := hb2
    _ = 16 * K1 / cmin * (Real.log (|t| + 3)) ^ (2 : ℕ) := by rw [hL]

end

end Work.FIArea6Hecke.R
