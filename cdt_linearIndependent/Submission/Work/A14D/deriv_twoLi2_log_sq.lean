import Mathlib
import Submission.Work.A14D.ppc_aux

/-!
# `Work.A14D.deriv_twoLi2_log_sq`

The derivative of the analytic function
`w ↦ 2·Li₂(w) + (1/2)·log(1−w)²` on the unit disc, where `Li₂ = Work.C7.Li2ps` is the formal
dilogarithm series.

Since `d/dw Li₂(w) = −log(1−w)/w` and `d/dw log(1−w)² = −2 log(1−w)/(1−w)`, we get

`d/dw (2·Li₂ + (1/2)·log(1−w)²) = −(z−2)·log(1−z)/(z(z−1))`.

The only non-trivial ingredient is the value `evp (deriv Li₂) z = −log(1−z)/z`, obtained by
shifting the index in the absolutely convergent series and comparing with `hasSum_Lps`.
-/

namespace Work.A14D

open Complex Metric
open scoped BigOperators

noncomputable section

/-- Shifting the index in an absolutely convergent power series: multiplying by `y` inside the
sum equals replacing `a n` by `a (n-1)` termwise. -/
private lemma tsum_mul_pow_shift (a : ℕ → ℂ) (y : ℂ) (h : Summable fun n => a n * y ^ n) :
    y * (∑' n, a n * y ^ n) = ∑' n, (if n = 0 then 0 else a (n - 1)) * y ^ n := by
  have hmul : y * (∑' n, a n * y ^ n) = ∑' n, a n * y ^ (n + 1) := by
    rw [← Summable.tsum_mul_left y h]
    exact tsum_congr (fun n => by ring)
  rw [hmul]
  set b : ℕ → ℂ := fun n => (if n = 0 then 0 else a (n - 1)) * y ^ n with hb
  have hb0 : b 0 = 0 := by simp [hb]
  have hb1 : ∀ n : ℕ, b (n + 1) = a n * y ^ (n + 1) := by intro n; simp [hb]
  have hsum_shift : Summable fun n => b (n + 1) := by
    rw [show (fun n => b (n + 1)) = fun n => a n * y ^ (n + 1) from funext hb1]
    exact (h.mul_right y).congr (fun n => by ring)
  have hSb : Summable b := (summable_nat_add_iff 1).mp hsum_shift
  have hshift : HasSum (fun n => b (n + 1)) (∑' n, b n) := by
    have h' := (hasSum_nat_add_iff' (f := b) 1).mpr hSb.hasSum
    rwa [Finset.sum_range_one, hb0, sub_zero] at h'
  rw [← hshift.tsum_eq]
  exact tsum_congr hb1

/-- Coefficient shift for the dilogarithm: the `(n-1)`-st coefficient of `Li₂'` is the `n`-th
coefficient of `−Lps`. -/
private lemma coeff_deriv_Li2ps_shift (n : ℕ) :
    (if n = 0 then (0 : ℂ)
        else ((PowerSeries.coeff (n - 1) (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) : ℚ) : ℂ))
      = -(((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ)) := by
  rcases n with _ | m
  · rw [if_pos rfl, Work.C7.coeff_zero_Lps]
    norm_num
  · have hm : m + 1 - 1 = m := by omega
    rw [if_neg (by omega : ¬ (m + 1 = 0)), hm, Work.C7.coeff_deriv_Li2ps,
      Work.C7.coeff_Lps, if_neg (by omega : ¬ (m + 1 = 0))]
    push_cast
    ring

/-- The value at `z` of the coefficient series of `Li₂'`: `Σ zⁿ/(n+1) = −log(1−z)/z`. -/
private theorem evp_deriv_Li2ps_val {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) z = -Complex.log (1 - z) / z := by
  obtain ⟨C, hC, k, hk⟩ := poly_growth_Li2ps
  obtain ⟨C', hC', k', hk'⟩ := poly_growth_deriv hC hk
  have hS : Summable (fun n : ℕ =>
      ((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n) :=
    (summable_abs_coeff_of_poly_growth hC' hk' hz).of_norm
  have hshift := tsum_mul_pow_shift
    (fun n : ℕ => ((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) : ℚ) : ℂ)) z hS
  have hR : (∑' n : ℕ, (if n = 0 then (0 : ℂ)
        else ((PowerSeries.coeff (n - 1) (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) : ℚ) : ℂ))
          * z ^ n) = -Complex.log (1 - z) := by
    have h1 : (∑' n : ℕ, (if n = 0 then (0 : ℂ)
          else ((PowerSeries.coeff (n - 1) (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) : ℚ) : ℂ))
            * z ^ n)
        = ∑' n : ℕ, -(((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n) := by
      refine tsum_congr fun n => ?_
      rw [coeff_deriv_Li2ps_shift n, neg_mul]
    rw [h1, tsum_neg]
    congr 1
    exact Work.C7.evA_Lps hz
  have hmain : z * Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) z
      = -Complex.log (1 - z) := by
    have h := hshift
    rw [hR] at h
    exact h
  rw [eq_div_iff hz0, mul_comm]
  exact hmain

theorem deriv_twoLi2_log_sq (z : ℂ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ => 2 * Work.CPull.evp Work.C7.Li2ps w
        + (1 / 2) * (Complex.log (1 - w)) ^ 2)
      (-(z - 2) * Complex.log (1 - z) / (z * (z - 1))) z := by
  obtain ⟨C, hC, k, hk⟩ := poly_growth_Li2ps
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz
  -- derivative of `w ↦ evp Li2ps w`
  have hF : HasDerivAt (fun w : ℂ => Work.CPull.evp Work.C7.Li2ps w)
      (Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) z) z := by
    have h := (differentiableOn_evp_of_poly_growth hC hk).differentiableAt
      (Metric.isOpen_ball.mem_nhds hzmem)
    have hh := h.hasDerivAt
    rw [← evp_deriv (f := Work.C7.Li2ps) hC hk hz] at hh
    exact hh
  -- derivative of `w ↦ log(1-w)^2`
  have hlogsq : HasDerivAt (fun w : ℂ => (Complex.log (1 - w)) ^ 2)
      (2 * Complex.log (1 - z) * (z - 1)⁻¹) z := by
    have h1 : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) ((z - 1)⁻¹) z :=
      hasDerivAt_log_one_sub hz
    have hp := h1.pow 2
    have hf : ((fun w : ℂ => Complex.log (1 - w)) ^ 2)
        = fun w : ℂ => (Complex.log (1 - w)) ^ 2 := by
      funext w; rw [Pi.pow_apply]
    rw [hf] at hp
    rw [show (((2 : ℕ) : ℂ) * Complex.log (1 - z) ^ (2 - 1) * (z - 1)⁻¹)
        = 2 * Complex.log (1 - z) * (z - 1)⁻¹ by norm_num] at hp
    exact hp
  have hG : HasDerivAt (fun w : ℂ => (1 / 2) * (Complex.log (1 - w)) ^ 2)
      ((1 / 2) * (2 * Complex.log (1 - z) * (z - 1)⁻¹)) z := hlogsq.const_mul (1 / 2)
  have htotal := (hF.const_mul 2).add hG
  refine htotal.congr_deriv ?_
  rw [evp_deriv_Li2ps_val hz hz0]
  have hz1 : z - 1 ≠ 0 := by
    intro hh
    have hz1' : z = 1 := sub_eq_zero.mp hh
    rw [hz1'] at hz
    simp at hz
  field_simp
  ring

end

end Work.A14D
