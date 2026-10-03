import Mathlib.Analysis.Complex.Liouville
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

open Complex Metric
open scoped Real

noncomputable section

namespace Commons.NumberTheory.LSeries

/-!
# A `(log |t|)^2` bound for the derivative of the Riemann zeta function
in the zero-free region

We prove that there is an absolute constant `C > 0` such that
`‖ζ'(σ + i t)‖ ≤ C · (log (|t| + 2))^2`
for all `2 ≤ |t|` and all `σ` in the (essentially) classical zero-free region
`1 - 1/(2 log(|t|+2)) ≤ σ ≤ 1 + 1/(2 log(|t|+2))`.

The proof is a pure Cauchy-estimate argument.  Write `L = log(|t|+2)`,
`s = σ + i t` and let `ρ = 1/(6L)`.  Choose `ρ` so small that the whole disc
`B(s,ρ)` still projects onto the strip `re w ≥ 1/2` and `|im w| ≥ 1`.  On that
disc:

* if `re w ≤ 1`, the fractional bound `‖ζ(w)‖ ≤ C |im w|^{1 - re w} log|im w|
  (from the commons) applies; since `1 - re w ≤ 1/L` and `|im w| ≤ |t| + 2 = e^L`
  the power factor is at most `e`;
* if `re w ≥ 1`, the logarithmic bound `‖ζ(w)‖ ≤ 5 log(|im w| + 2)` applies.

Hence `‖ζ(w)‖ ≤ M` on `B(s,ρ)` with `M ≤ max 5 (C e) · 2L`, and Cauchy's
estimate `‖ζ'(s)‖ ≤ M/ρ` gives `‖ζ'(s)‖ ≤ 12 · max 5 (C e) · L^2`.
-/

theorem exists_bound_deriv_riemannZeta_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - 1 / (2 * Real.log (|t| + 2)) ≤ σ →
      σ ≤ 1 + 1 / (2 * Real.log (|t| + 2)) →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (Real.log (|t| + 2)) ^ 2 := by
  obtain ⟨Cf, hCf0, hCf⟩ := exists_bound_norm_riemannZeta_fractional
  refine ⟨12 * max 5 (Cf * Real.exp 1), ?_, ?_⟩
  · have hpos : (0 : ℝ) < max 5 (Cf * Real.exp 1) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    positivity
  intro σ t ht hσlo hσhi
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hL_gt : (4 : ℝ) / 3 < L := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hle : Real.log 4 ≤ L := by
      rw [hLdef]
      exact Real.log_le_log (by norm_num)
        (by linarith [abs_nonneg t] : (4 : ℝ) ≤ |t| + 2)
    rw [h4] at hle
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 0 < L := by linarith
  have hLge1 : 1 ≤ L := by linarith
  have hlog2le : Real.log 2 ≤ L := by
    have := Real.log_two_lt_d9
    linarith
  set ρ : ℝ := 1 / (6 * L) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hρle6 : ρ ≤ 1 / 6 := by
    rw [hρdef]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6)
    nlinarith [hLge1]
  have hsum625 : 1 / (2 * L) + 1 / (6 * L) ≤ 1 / L := by
    have hkey : 1 / (2 * L) + 1 / (6 * L) = 2 / (3 * L) := by
      field_simp; ring
    rw [hkey, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * L)]
    rw [show 1 / L * (3 * L) = 3 by field_simp]
    norm_num
  have hsum_half : 1 / (2 * L) + 1 / (6 * L) ≤ 1 / 2 := by
    have hkey : 1 / (2 * L) + 1 / (6 * L) = 2 / (3 * L) := by
      field_simp; ring
    rw [hkey, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * L)]
    linarith [hL_gt]
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hs_re : s.re = σ := by simp [hsdef]
  have hs_im : s.im = t := by simp [hsdef]
  have hmem : ∀ w : ℂ, w ∈ Metric.sphere s ρ → ‖w - s‖ = ρ := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    exact hw
  -- lower bound on the real part on the sphere
  have hWre : ∀ w : ℂ, w ∈ Metric.sphere s ρ → (1 : ℝ) / 2 ≤ w.re := by
    intro w hw
    have hdist := hmem w hw
    have h1 : |(w - s).re| ≤ ρ := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [hdist] at h
      exact h
    have h2 : (w - s).re = w.re - σ := by simp [hs_re]
    rw [h2] at h1
    have h3 : σ - ρ ≤ w.re := by linarith [(abs_le.mp h1).1]
    linarith [hσlo, hsum_half, h3, hρdef]
  -- lower bound on |im| on the sphere
  have hWim : ∀ w : ℂ, w ∈ Metric.sphere s ρ → 1 ≤ |w.im| := by
    intro w hw
    have hdist := hmem w hw
    have h1 : |(w - s).im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [hdist] at h
      exact h
    have h2 : (w - s).im = w.im - t := by simp [hs_im]
    rw [h2] at h1
    have htri : |t| ≤ |w.im - t| + |w.im| := by
      have h := abs_add_le (t - w.im) w.im
      rw [sub_add_cancel, abs_sub_comm t w.im] at h
      exact h
    linarith [htri, h1, ht, hρle6]
  -- an upper bound for |im| (hence for log)
  have hWim_le : ∀ w : ℂ, w ∈ Metric.sphere s ρ → |w.im| ≤ |t| + 2 := by
    intro w hw
    have h1 : |(w - s).im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [hmem w hw] at h
      exact h
    have h2 : (w - s).im = w.im - t := by simp [hs_im]
    rw [h2] at h1
    have htri : |w.im| ≤ |w.im - t| + |t| := by
      simpa using abs_add_le (w.im - t) t
    linarith [htri, h1, hρle6]
  have hlogWle : ∀ w : ℂ, w ∈ Metric.sphere s ρ → Real.log (|w.im| + 2) ≤ 2 * L := by
    intro w hw
    have hle := hWim_le w hw
    have harg : |w.im| + 2 ≤ 2 * (|t| + 2) := by
      have := abs_nonneg t
      linarith
    calc Real.log (|w.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
          Real.log_le_log (by positivity) harg
      _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
      _ ≤ 2 * L := by linarith
  -- `1 - re w ≤ 1/L` on the sphere
  have h1mre : ∀ w : ℂ, w ∈ Metric.sphere s ρ → 1 - w.re ≤ 1 / L := by
    intro w hw
    have hdist := hmem w hw
    have h1 : |(w - s).re| ≤ ρ := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [hdist] at h
      exact h
    have h2 : (w - s).re = w.re - σ := by simp [hs_re]
    rw [h2] at h1
    have h3 : σ - ρ ≤ w.re := by linarith [(abs_le.mp h1).1]
    linarith [hσlo, hsum625, h3, hρdef]
  -- the sup bound on the sphere
  have hB : ∀ w ∈ Metric.sphere s ρ,
      ‖riemannZeta w‖ ≤ max 5 (Cf * Real.exp 1) * (2 * L) := by
    intro w hw
    have hre := hWre w hw
    have him := hWim w hw
    have hreL := h1mre w hw
    have hlog := hlogWle w hw
    have hlog_nonneg : 0 ≤ Real.log (|w.im| + 2) :=
      Real.log_nonneg (by have := abs_nonneg w.im; linarith)
    have hm5 : (5 : ℝ) ≤ max 5 (Cf * Real.exp 1) := le_max_left _ _
    have hmCf : Cf * Real.exp 1 ≤ max 5 (Cf * Real.exp 1) := le_max_right _ _
    have h2Lnonneg : (0 : ℝ) ≤ 2 * L := by linarith
    rcases le_or_gt (1 : ℝ) w.re with hge | hlt
    · have hb := norm_riemannZeta_le_five_mul_log (σ := w.re) (t := w.im) hge him
      rw [Complex.re_add_im w] at hb
      calc ‖riemannZeta w‖ ≤ 5 * Real.log (|w.im| + 2) := hb
        _ ≤ max 5 (Cf * Real.exp 1) * (2 * L) := by
            have h52 : 5 * Real.log (|w.im| + 2) ≤ 5 * (2 * L) := by linarith
            have h53 : 5 * (2 * L) ≤ max 5 (Cf * Real.exp 1) * (2 * L) :=
              mul_le_mul_of_nonneg_right hm5 h2Lnonneg
            linarith
    · have hle1 : w.re ≤ 1 := le_of_lt hlt
      have hb := hCf w.re w.im hre hle1 him
      rw [Complex.re_add_im w] at hb
      have hpow : |w.im| ^ (1 - w.re) ≤ Real.exp 1 := by
        have hstep1 : |w.im| ^ (1 - w.re) ≤ |w.im| ^ (1 / L) :=
          Real.rpow_le_rpow_of_exponent_le him hreL
        have hWi_le := hWim_le w hw
        have hstep2 : |w.im| ^ (1 / L) ≤ (|t| + 2) ^ (1 / L) :=
          Real.rpow_le_rpow (abs_nonneg w.im) hWi_le (by positivity)
        have hstep3 : (|t| + 2) ^ (1 / L) = Real.exp 1 := by
          rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < |t| + 2), hLdef,
            mul_one_div_cancel (ne_of_gt hLpos)]
        linarith [hstep1, hstep2, hstep3.le]
      calc ‖riemannZeta w‖ ≤ Cf * |w.im| ^ (1 - w.re) * Real.log (|w.im| + 2) := hb
        _ ≤ Cf * Real.exp 1 * Real.log (|w.im| + 2) := by
            apply mul_le_mul_of_nonneg_right _ hlog_nonneg
            exact mul_le_mul_of_nonneg_left hpow hCf0.le
        _ ≤ max 5 (Cf * Real.exp 1) * (2 * L) := by
            have h1 : Cf * Real.exp 1 * Real.log (|w.im| + 2) ≤
                Cf * Real.exp 1 * (2 * L) := mul_le_mul_of_nonneg_left hlog (by positivity)
            have h2 : Cf * Real.exp 1 * (2 * L) ≤
                max 5 (Cf * Real.exp 1) * (2 * L) :=
              mul_le_mul_of_nonneg_right hmCf h2Lnonneg
            linarith
  -- differentiability of ζ on the disc
  have hdiff : DiffContOnCl ℂ riemannZeta (Metric.ball s ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (ne_of_gt hρpos)]
    intro w hw
    have hwne : w ≠ 1 := by
      intro hw1
      have hmem' : ‖w - s‖ ≤ ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        exact hw
      rw [hw1] at hmem'
      have hge : (2 : ℝ) ≤ ‖(1 : ℂ) - s‖ := by
        calc (2 : ℝ) ≤ |t| := ht
          _ = |((1 : ℂ) - s).im| := by simp [hs_im]
          _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
      linarith [hρle6]
    exact (differentiableAt_riemannZeta hwne).differentiableWithinAt
  have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := riemannZeta) (c := s) (R := ρ) (C := max 5 (Cf * Real.exp 1) * (2 * L))
    hρpos hdiff hB
  calc ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖deriv riemannZeta s‖ := by rw [hsdef]
    _ ≤ (max 5 (Cf * Real.exp 1) * (2 * L)) / ρ := hCau
    _ = 12 * max 5 (Cf * Real.exp 1) * L ^ 2 := by
        rw [hρdef]
        field_simp
        ring

end Commons.NumberTheory.LSeries