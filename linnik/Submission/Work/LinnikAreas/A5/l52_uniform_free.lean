import Mathlib
import Submission.Commons.NumberTheory.Linnik.lemma5_2_sigma_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.far_zero_invSq_sum_uniform_delta
import Submission.Commons.NumberTheory.Linnik.smoothed_vonMangoldt_tsum_re
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.Calculus.norm_iteratedDeriv_two_exp_mul_real_le
import Submission.Commons.Analysis.Asymptotics.le_mul_exp_sqrt_log_eventually

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators
open Commons.NumberTheory.Linnik
open Commons.Analysis.Calculus

set_option maxHeartbeats 8000000

namespace Work.LinnikAreas.A5

attribute [local instance] Classical.propDecidable

private lemma near_mem_closedBall {t : ℝ} {u : ℂ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (h : ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall 0 (|t| + 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖u‖ ≤ ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖ := by
    calc ‖u‖ = ‖((1 : ℂ) + (t : ℂ) * Complex.I) - ((1 : ℂ) + (t : ℂ) * Complex.I - u)‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
    calc ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |t| := by
          rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  linarith only [hδ1, h, h1, h2]

/-- The univ-divisor of the completed L-function vanishes only at zeros, which lie in the strip. -/
private lemma div_univ_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ}
    (h : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u ≠ 0) :
    0 < u.re ∧ u.re < 1 := by
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hcast : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) ≠ 0 := by
    rw [← Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han (Set.mem_univ u)]
    exact h
  have haux : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 :=
    fun h0 => hcast (by simp [h0])
  exact completedL_zero_strip χ hχ hχprim (apply_eq_zero_of_analyticOrderNatAt_ne_zero haux)

/-- The univ-divisor of the completed L-function is non-negative (it counts multiplicities). -/
private lemma div_univ_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (u : ℂ) :
    (0 : ℝ) ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ)) : ℝ) := by
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han (Set.mem_univ u)]
  positivity

/-- Shifting the summation point by `β` and multiplying the weight by `exp (β L ·)` leaves the
smoothed von Mangoldt term `n^{-s} f (log n / L)` unchanged. -/
private lemma div_cpow_mul_exp_eq (β L : ℝ) (hL : 0 < L) (s : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℂ) ^ (s + (β : ℂ)))⁻¹ * ((Real.exp (β * L * (Real.log n / L)) : ℝ) : ℂ)
      = ((n : ℂ) ^ s)⁻¹ := by
  have hne : (n : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcβ : (n : ℂ) ^ (β : ℂ) = ((Real.exp (β * Real.log n) : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n) β, Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hexp : Real.exp (β * L * (Real.log n / L)) = Real.exp (β * Real.log n) := by
    congr 1
    field_simp
  rw [Complex.cpow_add s (β : ℂ) hne, hcβ, hexp, mul_inv_rev]
  have hb : ((Real.exp (β * Real.log n) : ℝ) : ℂ) ≠ 0 := by simp
  field_simp

/-- The Laplace-type integral of the shifted weight at the shifted point. -/
private lemma integral_shift_eq (β L x₀ : ℝ) (s u : ℂ) (f : ℝ → ℝ) :
    (∫ τ in (0:ℝ)..x₀,
        Complex.exp (-(((s + (β : ℂ) - u) * (L : ℂ)) * (τ : ℂ))) *
          (((Real.exp (β * L * τ) * f τ) : ℝ) : ℂ))
      = ∫ τ in (0:ℝ)..x₀,
          Complex.exp (-(((s - u) * (L : ℂ)) * (τ : ℂ))) * ((f τ : ℝ) : ℂ) := by
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  have hexp : Complex.exp (-(((s + (β : ℂ) - u) * (L : ℂ)) * (τ : ℂ))) *
        Complex.exp (((β * L * τ : ℝ)) : ℂ)
      = Complex.exp (-(((s - u) * (L : ℂ)) * (τ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc Complex.exp (-(((s + (β : ℂ) - u) * (L : ℂ)) * (τ : ℂ))) *
        (((Real.exp (β * L * τ) * f τ) : ℝ) : ℂ)
      = Complex.exp (-(((s + (β : ℂ) - u) * (L : ℂ)) * (τ : ℂ))) *
          (Complex.exp (((β * L * τ : ℝ)) : ℂ) * ((f τ : ℝ) : ℂ)) := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp]
    _ = (Complex.exp (-(((s + (β : ℂ) - u) * (L : ℂ)) * (τ : ℂ))) *
          Complex.exp (((β * L * τ : ℝ)) : ℂ)) * ((f τ : ℝ) : ℂ) := by ring
    _ = _ := by rw [hexp]

/-- **Wide crux, uniform in `B`.**  The same statement as
`Commons.NumberTheory.Linnik.explicitFormula_chi_gen_crux_wide`, but with the constant `C`
independent of the second-derivative bound `B` (the proof of the published version exhibits
`C = 100000`, which does not depend on `B`). -/
private theorem crux_wide_uniform (x₀ : ℝ) (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {f : ℝ → ℂ}
      (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {L : ℝ} (hL : 1 < L),
      ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L →
        DirichletCharacter.LFunction χ s ≠ 0 →
        ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              f (Real.log n / L))
          + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
                - f 0 / ((s - u) * (L : ℂ))))
          + f 0 * logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C *
            (B * x₀ + ‖f 0‖ / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro B hB N _ χ hχ hχprim f hcont hsupp hf2 hBnd L hL
  intro s hsre hLs
  have hLpos : (0:ℝ) < L := by linarith only [hL]
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlogLnn : (0:ℝ) ≤ Real.log L := hlogL.le
  -- The exponent range
  set δ : ℝ := Real.sqrt (Real.log L) / L with hδdef
  have hδnn : 0 ≤ δ := by rw [hδdef]; positivity
  have hlogLt : Real.log L < L^2/4 := by
    rcases eq_or_ne L 2 with h2 | h2
    · rw [h2]; linarith only [Real.log_two_lt_d9]
    · have h1 : Real.log L < L - 1 := Real.log_lt_sub_one_of_pos hLpos (by linarith only [hL])
      have h3 : L - 1 < L^2/4 := by
        have h4 : (0:ℝ) < (L-2)^2 := by positivity
        linarith only [h4]
      linarith only [h1, h3]
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδhalf : δ < 1/2 := by
    rw [hδdef, div_lt_iff₀ hLpos]
    have hsq : Real.sqrt (Real.log L) < L/2 := by
      rw [Real.sqrt_lt' (by linarith only [hL] : (0:ℝ) < L/2)]
      linarith only [hlogLt]
    linarith only [hsq]
  set α : ℝ := 1 + 2*δ with hαdef
  have hα1 : 1 < α := by rw [hαdef]; linarith only [hδpos]
  have hα2 : α < 2 := by rw [hαdef]; linarith only [hδhalf]
  have hsr : s.re - 1 ≤ δ := (abs_le.mp hsre).2
  have hsrg : -(δ) ≤ s.re - 1 := (abs_le.mp hsre).1
  have hασ : s.re < α := by rw [hαdef]; linarith only [hδpos, hsr]
  have hsrepos : 0 < s.re := by linarith only [hδpos, hδhalf, hsrg]
  have hsre_half : (1:ℝ)/2 ≤ s.re := by linarith only [hδhalf, hsrg]
  have hnorm_half : (1:ℝ)/2 ≤ ‖s‖ := le_trans hsre_half (Complex.re_le_norm s)
  -- abbreviations
  set lg : ℝ := Real.log (2 + ‖s‖) with hlgdef
  have hlgpos : 0 < lg := by
    rw [hlgdef]
    apply Real.log_pos
    have : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    linarith only [hδpos, hδhalf, hnorm_half]
  have hlg2 : Real.log 2 ≤ lg := by
    rw [hlgdef]
    apply Real.log_le_log (by norm_num)
    have : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    linarith only [hδpos, hδhalf, hnorm_half]
  set A : ℝ := 3 * B * x₀ + 2 * ‖f 0‖ / x₀ with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  -- the three ingredients
  have hline :=
    Commons.NumberTheory.DirichletCharacter.smoothed_vonMangoldt_eq_line_regularized
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL hα1 hασ
  have hshift :=
    Commons.NumberTheory.DirichletCharacter.regularized_divisor_contour_shift_gen
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL hα1 hα2 hασ
      (by linarith only [hδpos, hδhalf, hsrg] : -(1/2:ℝ) < s.re) hLs
  have hleft :=
    Commons.Analysis.Complex.regularized_leftEdge_bound_alt
      (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hsupp χ hχ hχprim hL (by linarith only [hδpos, hδhalf, hsrg] : (0:ℝ) < s.re + 1/2)
  -- name the three integrals
  set Ia : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) with hIadef
  set Il : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) with hIldef
  set Φ0 : ℂ := (∫ t in (0:ℝ)..x₀, Complex.exp (-((s - 0) * (L : ℂ) * (t : ℂ))) * f t)
      - f 0 / ((s - 0) * (L : ℂ)) with hΦ0def
  -- rewrite the ingredients
  have hline' : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
        f (Real.log n / L))
      = -(L / (2 * (Real.pi : ℂ))) * Ia := by
    rw [hIadef]; exact hline
  have hshift' :
      (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ))))
        = (1 / (2 * (Real.pi : ℂ))) * (Ia - Il)
          - logDeriv (DirichletCharacter.LFunction χ) s * (f 0 / (L : ℂ))
          - (if χ.Even then Φ0 else 0) := by
    rw [hIadef, hIldef]
    rw [hΦ0def]
    exact hshift
  have hleft' : ‖Il‖ ≤ A / L^2 * 2000 * (lg + 1) := by
    rw [hIldef, hAdef, hlgdef]; exact hleft
  have hΦ0b : ‖Φ0‖ ≤ A / (L^2 * ‖s‖^2) := by
    rw [hΦ0def, hAdef]
    have hz : 0 < (s * (L:ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_pos hsrepos hLpos
    have h := Commons.Analysis.Complex.lapX_sub_inv_bound
      (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2 hBnd hsupp (z := s * (L:ℂ)) hz
    have hnorm : ‖s * (L:ℂ)‖^2 = L^2 * ‖s‖^2 := by
      rw [norm_mul, Complex.norm_of_nonneg hLpos.le]; ring
    rw [hnorm] at h
    simpa using h
  have hifb : ‖(if χ.Even then Φ0 else 0)‖ ≤ A / (L^2 * ‖s‖^2) := by
    by_cases h : χ.Even
    · simp only [if_pos h]; exact hΦ0b
    · simp only [if_neg h, norm_zero]; positivity
  -- the main identity
  have hmain :
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
            f (Real.log n / L))
        + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
              - f 0 / ((s - u) * (L : ℂ))))
        + f 0 * logDeriv (DirichletCharacter.LFunction χ) s
      = -(L / (2 * (Real.pi : ℂ))) * Il - (L : ℂ) * (if χ.Even then Φ0 else 0) := by
    rw [hline', hshift']
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLpos.ne'
    have hpi2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  rw [hmain]
  -- the bound
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlg_half : (1:ℝ)/2 ≤ lg := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by have := norm_nonneg s; linarith only [hδpos, hδhalf, hnorm_half] : (2:ℝ) ≤ 2 + ‖s‖)
    rw [hlgdef]
    linarith only [Real.log_two_gt_d9, hδpos, hδhalf, hlg2]
  have h1s : 1 / ‖s‖^2 ≤ 4 := by
    have h2 : (1:ℝ)/4 ≤ ‖s‖^2 := by nlinarith only [hnorm_half, norm_nonneg s]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s‖^2)]
    linarith only [h2]
  have hALnn : (0:ℝ) ≤ A / L := by positivity
  have heq1 : (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1))
      = (A / L) * (1000 / Real.pi) * (lg + 1) := by
    field_simp
    ring
  have heq2 : L * (A / (L^2 * ‖s‖^2)) = (A / L) * (1 / ‖s‖^2) := by
    field_simp
    try ring
  have hinvL : L⁻¹ ≤ (Real.log L) ^ (-(1/2 : ℝ)) := by
    have hsq : Real.sqrt (Real.log L) ≤ L := by
      rw [Real.sqrt_le_iff]
      refine ⟨hLpos.le, ?_⟩
      have := Real.log_le_sub_one_of_pos hLpos
      linarith only [hLpos, sq_nonneg (L - 1), hlogL, hlogLt]
    have hspos : 0 < Real.sqrt (Real.log L) := Real.sqrt_pos.mpr hlogL
    have h1 : (Real.log L) ^ (-(1/2 : ℝ)) = (Real.sqrt (Real.log L))⁻¹ := by
      rw [Real.rpow_neg hlogLnn, Real.sqrt_eq_rpow]
    rw [h1]
    exact (inv_le_inv₀ hLpos hspos).mpr hsq
  have hleft' : ‖Il‖ ≤ A / L^2 * 2000 * (lg + 1) := by
    rw [hIldef, hAdef, hlgdef]; exact hleft
  have hΦ0b : ‖Φ0‖ ≤ A / (L^2 * ‖s‖^2) := by
    rw [hΦ0def, hAdef]
    have hz : 0 < (s * (L:ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_pos hsrepos hLpos
    have h := Commons.Analysis.Complex.lapX_sub_inv_bound
      (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2 hBnd hsupp (z := s * (L:ℂ)) hz
    have hnorm : ‖s * (L:ℂ)‖^2 = L^2 * ‖s‖^2 := by
      rw [norm_mul, Complex.norm_of_nonneg hLpos.le]; ring
    rw [hnorm] at h
    simpa using h
  have hifb : ‖(if χ.Even then Φ0 else 0)‖ ≤ A / (L^2 * ‖s‖^2) := by
    by_cases h : χ.Even
    · simp only [if_pos h]; exact hΦ0b
    · simp only [if_neg h, norm_zero]; positivity
  have hLy : ‖(L / (2 * (Real.pi : ℂ))) * Il‖ ≤ (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) := by
    rw [norm_mul]
    have hc : ‖(L : ℂ) / (2 * (Real.pi : ℂ))‖ = L / (2 * Real.pi) := by
      rw [show (L : ℂ) / (2 * (Real.pi : ℂ)) = ((L / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_of_nonneg (show (0:ℝ) ≤ L / (2 * Real.pi) by positivity)]
    rw [hc]
    exact mul_le_mul_of_nonneg_left hleft' (by positivity)
  have hLb : ‖(L : ℂ) * (if χ.Even then Φ0 else 0)‖ ≤ L * (A / (L^2 * ‖s‖^2)) := by
    rw [norm_mul, Complex.norm_of_nonneg hLpos.le]
    exact mul_le_mul_of_nonneg_left hifb hLpos.le
  -- the numerical steps
  set P : ℝ := (3000 / Real.pi) + 12 with hPdef
  set Q : ℝ := B * x₀ + ‖f 0‖ / x₀ + 1 with hQdef
  set M : ℝ := (Real.log L) ^ (-(1/2 : ℝ)) with hMdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hMnn : 0 ≤ M := by rw [hMdef]; exact Real.rpow_nonneg hlogLnn _
  have hA3 : A ≤ 3 * Q := by
    rw [hAdef, hQdef]
    have h1 : (0:ℝ) ≤ ‖f 0‖ / x₀ := by positivity
    have h2 : (2:ℝ) * ‖f 0‖ / x₀ = 2 * (‖f 0‖ / x₀) := by ring
    rw [h2]
    linarith only [hδpos, hδhalf, h1]
  have hALbound : A / L ≤ 3 * Q * M := by
    have h1 : A / L ≤ 3 * Q / L := by
      rw [div_le_div_iff₀ hLpos hLpos]; nlinarith only [hA3, hL]
    have h2 : 3 * Q / L ≤ 3 * Q * M := by
      rw [div_eq_mul_inv, hMdef]
      exact mul_le_mul_of_nonneg_left hinvL (by positivity)
    linarith only [h1, h2]
  have hstep1 : (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) + L * (A / (L^2 * ‖s‖^2))
      ≤ (A / L) * P * lg := by
    rw [heq1, heq2]
    have h1 : (A / L) * (1000 / Real.pi) * (lg + 1) ≤ (A / L) * (1000 / Real.pi) * (3 * lg) := by
      have hc : (0:ℝ) ≤ (A / L) * (1000 / Real.pi) := by positivity
      have h5 : lg + 1 ≤ 3 * lg := by linarith only [hlg_half]
      exact mul_le_mul_of_nonneg_left h5 hc
    have h2 : (A / L) * (1 / ‖s‖^2) ≤ (A / L) * (12 * lg) := by
      have h4 : 1 / ‖s‖^2 ≤ 12 * lg := by linarith only [hδpos, hδhalf, hlg_half, h1s]
      exact mul_le_mul_of_nonneg_left h4 hALnn
    have h3 : (A / L) * (1000 / Real.pi) * (3 * lg) + (A / L) * (12 * lg) = (A / L) * P * lg := by
      rw [hPdef]; ring
    linarith only [h1, h2, h3.le, h3.ge, h3]
  have hstep2 : (A / L) * P * lg ≤ 3 * P * Q * M * lg := by
    have hc : (0:ℝ) ≤ P * lg := by rw [hPdef]; positivity
    have h := mul_le_mul_of_nonneg_right hALbound hc
    calc (A / L) * P * lg = (A / L) * (P * lg) := by ring
      _ ≤ 3 * Q * M * (P * lg) := h
      _ = 3 * P * Q * M * lg := by ring
  have hstep3 : 3 * P * Q * M * lg ≤ 100000 * Q * M * lg := by
    have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h1 : 3 * P ≤ 100000 := by
      rw [hPdef]
      have h2 : 3000 / Real.pi < 1000 := by
        rw [div_lt_iff₀ (by linarith only [hδpos, hδhalf, hpi] : (0:ℝ) < Real.pi)]
        linarith only [hpi]
      linarith only [hδpos, hδhalf, h2]
    have hc : (0:ℝ) ≤ Q * M * lg := by positivity
    have h := mul_le_mul_of_nonneg_right h1 hc
    calc 3 * P * Q * M * lg = (3 * P) * (Q * M * lg) := by ring
      _ ≤ 100000 * (Q * M * lg) := h
      _ = 100000 * Q * M * lg := by ring
  calc ‖-(L / (2 * (Real.pi : ℂ))) * Il - (L : ℂ) * (if χ.Even then Φ0 else 0)‖
      ≤ ‖(L / (2 * (Real.pi : ℂ))) * Il‖ + ‖(L : ℂ) * (if χ.Even then Φ0 else 0)‖ := by
        simpa only [neg_mul, norm_neg] using
          norm_sub_le (-((L / (2 * (Real.pi : ℂ))) * Il)) ((L : ℂ) * (if χ.Even then Φ0 else 0))
    _ ≤ (L / (2 * Real.pi)) * (A / L^2 * 2000 * (lg + 1)) + L * (A / (L^2 * ‖s‖^2)) := add_le_add hLy hLb
    _ ≤ (A / L) * P * lg := hstep1
    _ ≤ 3 * P * Q * M * lg := hstep2
    _ ≤ 100000 * Q * M * lg := hstep3
    _ = 100000 * (B * x₀ + ‖f 0‖ / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
        rw [hQdef, hMdef, hlgdef]

/-- **Wide general smoothed explicit formula, uniform in `B`.** -/
private theorem explicitFormula_chi_gen_wide_uniform (x₀ : ℝ) (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {f : ℝ → ℝ}
      (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {L : ℝ} (hL : 1 < L),
      ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L →
        DirichletCharacter.LFunction χ s ≠ 0 →
        ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              ((f (Real.log n / L) : ℝ) : ℂ))
          + L * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))
                - ((f 0 : ℝ) : ℂ) / ((s - u) * L)))
          + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C * (B * x₀ + |f 0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
  obtain ⟨C, hCpos, hC⟩ := crux_wide_uniform x₀ hx₀
  refine ⟨C, hCpos, ?_⟩
  intro B hB N _ χ hχ hχprim f hcont hsupp hf2 hBnd L hL s hsre hLs
  set g : ℝ → ℂ := fun t => ((f t : ℝ) : ℂ) with hgdef
  have hcontg : ContinuousOn g (Set.Icc 0 x₀) := by
    change ContinuousOn (fun t => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀)
    exact Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
  have hsuppg : ∀ t : ℝ, x₀ ≤ t → g t = 0 := by
    intro t ht; rw [hgdef]; simp [hsupp t ht]
  have hf2g : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) x₀) := by
    change ContDiffOn ℝ 2 (fun t => ((f t : ℝ) : ℂ)) (Set.Ioo (0:ℝ) x₀)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf2
  have hBndg : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 g t‖ ≤ B := by
    intro t ht
    change ‖iteratedDeriv 2 (fun s => ((f s : ℝ) : ℂ)) t‖ ≤ B
    exact norm_ofReal_iteratedDeriv_two_le hf2 ht (hBnd t ht)
  have key := hC B hB χ hχ hχprim hcontg hsuppg hf2g hBndg hL s hsre hLs
  have hLHS : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
            g (Real.log n / L))
        + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * g t)
              - g 0 / ((s - u) * (L : ℂ))))
        + g 0 * logDeriv (DirichletCharacter.LFunction χ) s
      = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
              ((f (Real.log n / L) : ℝ) : ℂ))
          + L * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
              ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))
                - ((f 0 : ℝ) : ℂ) / ((s - u) * L)))
          + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s := by
    simp only [hgdef]
  rw [hLHS] at key
  have hg0 : ‖g 0‖ / x₀ = |f 0| / x₀ := by
    rw [hgdef]
    simp [Complex.normSq_ofReal]
  rw [hg0] at key
  exact key
/-- The purely numerical core of the absorption argument (wide-range version).

Under the key estimates `|α| ≤ sqrt (log L) + 1` and `spn ≤ 2 + 10 L`, the two error terms of the
shifted explicit formula are absorbed by `f0 * (ε/2) * L`, given the (subpolynomial) absorption
hypothesis. -/
private lemma numeric_core_wide {x₀ B f0 ε L α spn Bg Ag Cef cF D0 D2 Kc Pc : ℝ}
    (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hf0 : 0 < f0) (hε : 0 < ε) (hL5 : 5 ≤ L)
    (ha : |α| ≤ Real.sqrt (Real.log L) + 1) (hspn : spn ≤ 2 + 10 * L) (hspn0 : 0 ≤ spn)
    (hCef : 0 < Cef) (hcF : 0 < cF)
    (hBg : Bg = Real.exp (|α| * x₀) * (B + 2 * |α| * (B * x₀ + |f0| / x₀) + |α| ^ 2 * (B * x₀ ^ 2 + |f0|)))
    (hAg : Ag = 3 * Bg * x₀ + 2 * |f0| / x₀)
    (hD0 : D0 = B + 2 * (B * x₀ + |f0| / x₀) + (B * x₀ ^ 2 + |f0|) + 1)
    (hD2 : D2 = 3 * x₀ + 2 * |f0| / x₀)
    (hKc : Kc = (Real.log (Real.log 3)) ^ (-(1/2 : ℝ)))
    (hPc : Pc = D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)))
    (habsorb : Pc * Real.exp (x₀ * (Real.sqrt (Real.log L) + 1)) * (1 + Real.log L) ^ 5
      ≤ f0 * (ε / 2) * L) :
    (Ag / L) * (cF * (L + Real.log (2 + spn) + 2))
      + Cef * (Bg * x₀ + |f0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + spn)
      ≤ f0 * (ε / 2) * L := by
  have hLpos : 0 < L := by linarith only [hL5]
  have hL1 : 1 ≤ L := by linarith only [hL5]
  have hlogLnn : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL5])
  have hlogL1 : 1 ≤ Real.log L := by
    have hexp1 : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_three]
    have h5 : (1:ℝ) ≤ Real.log 5 := by
      have h := Real.log_le_log (Real.exp_pos 1) hexp1.le
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 5) hL5
    linarith only [h5, h]
  have hlogLpos : 0 < Real.log L := by linarith only [hlogL1]
  have hu0 : (0:ℝ) ≤ 1 + Real.log L := by linarith only [hlogL1]
  have hu1 : (1:ℝ) ≤ 1 + Real.log L := by linarith only [hlogL1]
  have hlog3gt1 : (1:ℝ) < Real.log 3 := by
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  have hloglog3pos : 0 < Real.log (Real.log 3) := Real.log_pos hlog3gt1
  have hKcpos : 0 < Kc := by
    rw [hKc, Real.rpow_neg hloglog3pos.le, ← Real.sqrt_eq_rpow]
    exact inv_pos.mpr (Real.sqrt_pos.mpr hloglog3pos)
  -- abbreviations
  set Q : ℝ := Real.exp (x₀ * (Real.sqrt (Real.log L) + 1)) with hQdef
  set Y : ℝ := B * x₀ + |f0| / x₀ with hYdef
  set Z : ℝ := B * x₀ ^ 2 + |f0| with hZdef
  set W : ℝ := B + 2 * |α| * (B * x₀ + |f0| / x₀) + |α| ^ 2 * (B * x₀ ^ 2 + |f0|) with hWdef
  have hQ0 : 0 ≤ Q := Real.exp_nonneg _
  have hQ1 : 1 ≤ Q := by
    rw [hQdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact add_nonneg (mul_nonneg hB hx₀.le) (by positivity)
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact add_nonneg (mul_nonneg hB (sq_nonneg x₀)) (abs_nonneg _)
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hBg' : Bg = Real.exp (|α| * x₀) * W := by rw [hBg, hWdef]
  have hW' : W = B + 2 * |α| * Y + |α| ^ 2 * Z := by rw [hWdef, hYdef, hZdef]
  have hD0' : D0 = B + 2 * Y + Z + 1 := by rw [hD0, hYdef, hZdef]
  have hD0ge1 : 1 ≤ D0 := by rw [hD0']; linarith only [hB, hY0, hZ0]
  have hD0nn : 0 ≤ D0 := by linarith only [hD0ge1]
  have hD2nn : 0 ≤ D2 := by rw [hD2]; positivity
  have hlogspn0 : 0 ≤ Real.log (2 + spn) := Real.log_nonneg (by linarith only [hspn0])
  have hlogsp : Real.log (2 + spn) ≤ 3 * (1 + Real.log L) := by
    have h1 : 2 + spn ≤ 4 + 10 * L := by linarith only [hspn]
    have hB15 : (15:ℝ) ≤ L ^ 2 - 10 := by nlinarith only [hL5]
    have hC75 : (75:ℝ) ≤ L * (L ^ 2 - 10) := by
      have h := mul_le_mul hL5 hB15 (by norm_num : (0:ℝ) ≤ 15) (by linarith only [hL5] : (0:ℝ) ≤ L)
      norm_num at h
      exact h
    have hD75 : L * (L ^ 2 - 10) = L ^ 3 - 10 * L := by ring
    have h2 : 4 + 10 * L ≤ L ^ 3 := by linarith only [hC75, hD75]
    have h3 : (0:ℝ) < 2 + spn := by linarith only [hspn0]
    have h4 : Real.log (2 + spn) ≤ Real.log (L ^ 3) := Real.log_le_log h3 (le_trans h1 h2)
    have h5 : Real.log (L ^ 3) = 3 * Real.log L := by
      rw [Real.log_pow]; push_cast; ring
    rw [h5] at h4
    linarith only [h4, hlogLnn]
  have hsle : Real.sqrt (Real.log L) ≤ Real.log L := by
    refine Real.sqrt_le_iff.mpr ⟨hlogLnn, ?_⟩
    have h := mul_le_mul_of_nonneg_left hlogL1 hlogLnn
    simpa [pow_two] using h
  have ha1 : |α| ≤ 1 + Real.log L := by linarith only [ha, hsle]
  have hαsq : |α| ^ 2 ≤ 4 * (1 + Real.log L) := by
    have hs2 : (Real.sqrt (Real.log L)) ^ 2 = Real.log L := Real.sq_sqrt hlogLnn
    have h2s : 2 * Real.sqrt (Real.log L) ≤ 2 * Real.log L := by linarith only [hsle]
    have h2 : (Real.sqrt (Real.log L) + 1) ^ 2 ≤ 4 * (1 + Real.log L) := by
      linarith only [hs2, h2s, hlogLnn]
    calc |α| ^ 2 ≤ (Real.sqrt (Real.log L) + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ ≤ 4 * (1 + Real.log L) := h2
  have hfac : W ≤ 4 * (1 + Real.log L) * (B + 2 * Y + Z + 1) := by
    have h1 : B ≤ (1 + Real.log L) * B := le_mul_of_one_le_left hB hu1
    have h2 : 2 * |α| * Y ≤ (1 + Real.log L) * (2 * Y) := by
      have h2Y : 0 ≤ 2 * Y := by linarith only [hY0]
      have h9 : |α| * (2 * Y) ≤ (1 + Real.log L) * (2 * Y) := mul_le_mul_of_nonneg_right ha1 h2Y
      have e : 2 * |α| * Y = |α| * (2 * Y) := by ring
      linarith only [h9, e]
    have h3 : |α| ^ 2 * Z ≤ 4 * (1 + Real.log L) * Z := mul_le_mul_of_nonneg_right hαsq hZ0
    have h4 : W ≤ (1 + Real.log L) * B + (1 + Real.log L) * (2 * Y) + 4 * (1 + Real.log L) * Z := by
      rw [hW']; linarith only [h1, h2, h3]
    have h5 : (1 + Real.log L) * B + (1 + Real.log L) * (2 * Y) + 4 * (1 + Real.log L) * Z
        ≤ 4 * (1 + Real.log L) * (B + 2 * Y + Z + 1) := by
      nlinarith only [hu0, hB, hY0, hZ0]
    linarith only [h4, h5]
  have hexp : Real.exp (|α| * x₀) ≤ Q := by
    rw [hQdef]
    refine Real.exp_le_exp.mpr ?_
    calc |α| * x₀ ≤ (Real.sqrt (Real.log L) + 1) * x₀ := mul_le_mul_of_nonneg_right ha hx₀.le
      _ = x₀ * (Real.sqrt (Real.log L) + 1) := by ring
  have hfac2 : 1 ≤ 4 * Q * (1 + Real.log L) * D0 := by
    have h3 : 1 ≤ Q * (1 + Real.log L) * D0 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ1 hu1) hD0ge1
    linarith only [h3]
  have hBg_le : Bg ≤ 4 * Q * (1 + Real.log L) * D0 := by
    rw [hBg', hD0']
    have hstep : Real.exp (|α| * x₀) * W ≤ Q * (4 * (1 + Real.log L) * (B + 2 * Y + Z + 1)) :=
      mul_le_mul hexp hfac hW0 hQ0
    have heq : Q * (4 * (1 + Real.log L) * (B + 2 * Y + Z + 1))
        = 4 * Q * (1 + Real.log L) * (B + 2 * Y + Z + 1) := by ring
    linarith only [hstep, heq]
  have hAg_le : Ag ≤ 4 * Q * (1 + Real.log L) * D0 * D2 := by
    rw [hAg, hD2]
    have hx3 : (0:ℝ) ≤ 3 * x₀ := by linarith only [hx₀]
    have h3 : 3 * Bg * x₀ ≤ (4 * Q * (1 + Real.log L) * D0) * (3 * x₀) := by
      have h := mul_le_mul_of_nonneg_right hBg_le hx3
      have e : Bg * (3 * x₀) = 3 * Bg * x₀ := by ring
      linarith only [h, e]
    have h5 : 0 ≤ 2 * |f0| / x₀ := by positivity
    have h4 : 2 * |f0| / x₀ ≤ (4 * Q * (1 + Real.log L) * D0) * (2 * |f0| / x₀) := by
      have h := mul_le_mul_of_nonneg_right hfac2 h5
      simpa using h
    have h6 : (4 * Q * (1 + Real.log L) * D0) * (3 * x₀) + (4 * Q * (1 + Real.log L) * D0) * (2 * |f0| / x₀)
        = 4 * Q * (1 + Real.log L) * D0 * (3 * x₀ + 2 * |f0| / x₀) := by ring
    linarith only [h3, h4, h6]
  have hterm1 : (Ag / L) * (cF * (L + Real.log (2 + spn) + 2))
      ≤ 24 * cF * D2 * D0 * Q * (1 + Real.log L) ^ 2 := by
    have h1 : Ag / L ≤ (4 * Q * (1 + Real.log L) * D0 * D2) / L := by
      rw [div_le_div_iff_of_pos_right hLpos]; exact hAg_le
    have h2 : L + Real.log (2 + spn) + 2 ≤ 6 * L * (1 + Real.log L) := by
      have hL : L ≤ L * (1 + Real.log L) := by
        rw [mul_comm]; exact le_mul_of_one_le_left hLpos.le hu1
      have h3 : 3 * (1 + Real.log L) ≤ 3 * L * (1 + Real.log L) := by
        have h := mul_le_mul_of_nonneg_right hL1 (by positivity : (0:ℝ) ≤ 3 * (1 + Real.log L))
        have e1 : (1:ℝ) * (3 * (1 + Real.log L)) = 3 * (1 + Real.log L) := by ring
        have e2 : L * (3 * (1 + Real.log L)) = 3 * L * (1 + Real.log L) := by ring
        linarith only [h, e1, e2]
      have h4 : (2:ℝ) ≤ 2 * L * (1 + Real.log L) := by nlinarith only [hL1, hu1]
      linarith only [hlogsp, hL, h3, h4]
    have h2b : 0 ≤ L + Real.log (2 + spn) + 2 := by linarith only [hlogspn0, hLpos]
    have h3 : (Ag / L) * (cF * (L + Real.log (2 + spn) + 2))
        ≤ ((4 * Q * (1 + Real.log L) * D0 * D2) / L) * (cF * (6 * L * (1 + Real.log L))) :=
      mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hcF.le) (mul_nonneg hcF.le h2b)
        (div_nonneg (by positivity) hLpos.le)
    have h4 : ((4 * Q * (1 + Real.log L) * D0 * D2) / L) * (cF * (6 * L * (1 + Real.log L)))
        = 24 * cF * D2 * D0 * Q * (1 + Real.log L) ^ 2 := by
      field_simp; ring
    linarith only [h3, h4]
  have hslog : (Real.log L) ^ (-(1/2 : ℝ)) ≤ Kc := by
    rw [hKc]
    refine Real.rpow_le_rpow_of_nonpos hloglog3pos ?_ (by norm_num)
    have hlog3L : Real.log 3 ≤ L := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1)
      linarith only [h, hL5]
    exact Real.log_le_log (by linarith only [hlog3gt1] : (0:ℝ) < Real.log 3) hlog3L
  have hA : Bg * x₀ + |f0| / x₀ + 1 ≤ 4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1) := by
    have h1 : Bg * x₀ ≤ (4 * Q * (1 + Real.log L) * D0) * x₀ :=
      mul_le_mul_of_nonneg_right hBg_le hx₀.le
    have h5 : 0 ≤ |f0| / x₀ + 1 := by positivity
    have h2 : |f0| / x₀ + 1 ≤ (4 * Q * (1 + Real.log L) * D0) * (|f0| / x₀ + 1) := by
      have h := mul_le_mul_of_nonneg_right hfac2 h5
      simpa using h
    have h6 : (4 * Q * (1 + Real.log L) * D0) * x₀ + (4 * Q * (1 + Real.log L) * D0) * (|f0| / x₀ + 1)
        = 4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1) := by ring
    linarith only [h1, h2, h6]
  have hterm2 : Cef * (Bg * x₀ + |f0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + spn)
      ≤ 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1) * D0 * Q * (1 + Real.log L) ^ 2 := by
    have hA0 : 0 ≤ 4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1) := by positivity
    have h6 : Cef * (Bg * x₀ + |f0| / x₀ + 1) ≤ Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) :=
      mul_le_mul_of_nonneg_left hA hCef.le
    have h6b : 0 ≤ Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) :=
      mul_nonneg hCef.le hA0
    have h7 : Cef * (Bg * x₀ + |f0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ))
        ≤ Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) * Kc :=
      mul_le_mul h6 hslog (Real.rpow_nonneg hlogLnn _) h6b
    have h8 : 0 ≤ Real.log (2 + spn) := hlogspn0
    have h9 : 0 ≤ Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) * Kc := mul_nonneg h6b hKcpos.le
    have h10 : Cef * (Bg * x₀ + |f0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + spn)
        ≤ Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) * Kc * (3 * (1 + Real.log L)) :=
      mul_le_mul h7 hlogsp h8 h9
    have h11 : Cef * (4 * Q * (1 + Real.log L) * D0 * (x₀ + |f0| / x₀ + 1)) * Kc * (3 * (1 + Real.log L))
        = 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1) * D0 * Q * (1 + Real.log L) ^ 2 := by ring
    linarith only [h10, h11]
  have hsum : (Ag / L) * (cF * (L + Real.log (2 + spn) + 2))
      + Cef * (Bg * x₀ + |f0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + spn)
      ≤ Pc * Q * (1 + Real.log L) ^ 5 := by
    have h5 : (1 + Real.log L) ^ 2 ≤ (1 + Real.log L) ^ 5 := by
      have h6 : (1:ℝ) ≤ 1 + Real.log L := hu1
      have h7 : (1:ℝ) ≤ (1 + Real.log L) ^ 3 := by
        calc (1:ℝ) = 1 ^ 3 := by norm_num
          _ ≤ (1 + Real.log L) ^ 3 := pow_le_pow_left₀ (by norm_num) h6 3
      calc (1 + Real.log L) ^ 2 = (1 + Real.log L) ^ 2 * 1 := by ring
        _ ≤ (1 + Real.log L) ^ 2 * (1 + Real.log L) ^ 3 := mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = (1 + Real.log L) ^ 5 := by ring
    have hmid : 24 * cF * D2 * D0 * Q * (1 + Real.log L) ^ 2
        + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1) * D0 * Q * (1 + Real.log L) ^ 2
        = D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q * (1 + Real.log L) ^ 2 := by ring
    have hfin : D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q * (1 + Real.log L) ^ 2
        ≤ Pc * Q * (1 + Real.log L) ^ 5 := by
      rw [hPc]
      have h7 : 0 ≤ D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q := by positivity
      have h8 := mul_le_mul_of_nonneg_left h5 h7
      have e1 : (D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q) * (1 + Real.log L) ^ 2
          = D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q * (1 + Real.log L) ^ 2 := by ring
      have e2 : (D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q) * (1 + Real.log L) ^ 5
          = D0 * (24 * cF * D2 + 12 * Kc * Cef * (x₀ + |f0| / x₀ + 1)) * Q * (1 + Real.log L) ^ 5 := by ring
      linarith only [h8, e1, e2]
    linarith only [hterm1, hterm2, hmid, hfin]
  exact le_trans hsum habsorb
/-
Threshold-uniform form of the smoothing estimate of HB §5 (PLMS 64 (1992)) with a free
smoothing parameter `L`, for a primitive non-principal Dirichlet character.

The quantitative inputs are available uniformly in the `C²`-bound `B ≥ 0` of the weight:

* `explicitFormula_chi_gen_wide_uniform` (below): the wide smoothed explicit formula, whose
  constant `100000` is independent of `B`, `χ`, `N`, `L` and the point `s`;
* `Commons.NumberTheory.DirichletCharacter.far_zero_invSq_sum_uniform_delta`: the uniform-in-`δ`
  far-zero inverse-square sum bound;
* `numeric_core_wide` (below): the purely numerical absorption of the two error terms into
  `f 0 · (ε/2) · L`, whose hypothesis is the subpolynomial estimate
  `le_mul_exp_sqrt_log_eventually`.

Since `f 0 = 1` and (by the two facts above) every constant in the argument depends only on
`(x₀, B, ε, δ)`, the witness `L₀` of the subpolynomial absorption can be chosen *before* `f` is
introduced, which yields a threshold uniform over all weights with the same data.  The proof is
otherwise the one of `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_param_free`
(shift `s` to `sp = (1 + η) + i·Im s`, apply the smoothed explicit formula there, split the
divisor sum into zeros within `δ` of `1 + i·Im s` and the far zeros, and absorb).
-/

theorem l52_uniform_free (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ L₀ : ℝ, ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
      (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      (hf0 : f 0 = 1)
      (hfbd : ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖f t‖ ≤ 1),
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
        {L : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L →
        (∀ s : ℂ, 1 + 1 / (L * Real.log L) ≤ s.re →
            s.re ≤ 1 + Real.log L / L →
            |s.im| ≤ 10 * L →
          (-logDeriv (DirichletCharacter.LFunction χ) s).re
            + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
            ≤ ((1/6 : ℝ) + ε/2) * L) →
        ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L →
          |s.im| ≤ 10 * L →
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ (n : ZMod N) / (n : ℂ) ^ s).re) * f (Real.log n / L))
            ≤ -L * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
                  ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
            + f 0 * ((1/6 : ℝ) + ε) * L := by
  classical
  obtain ⟨Cef, hCefpos, hEF⟩ := explicitFormula_chi_gen_wide_uniform x₀ hx₀
  obtain ⟨cF, hcFpos, hF⟩ :=
    Commons.NumberTheory.DirichletCharacter.far_zero_invSq_sum_uniform_delta
  set cF' : ℝ := cF / δ ^ 2 with hcF'def
  have hcF'pos : 0 < cF' := by rw [hcF'def]; positivity
  -- ===== numeric constants, computed *before* the weight `f` is introduced =====
  set D0 : ℝ := B + 2 * (B * x₀ + 1 / x₀) + (B * x₀ ^ 2 + 1) + 1 with hD0def
  have hD0nn : 0 ≤ D0 := by rw [hD0def]; positivity
  have hD0ge1 : 1 ≤ D0 := by
    rw [hD0def]
    have h1 : 0 ≤ B * x₀ := mul_nonneg hB hx₀.le
    have h2 : 0 ≤ B * x₀ ^ 2 := mul_nonneg hB (sq_nonneg x₀)
    have h3 : 0 ≤ 1 / x₀ := by positivity
    linarith only [hB, hδ0, hδ1, h1, h2, h3]
  set D2 : ℝ := 3 * x₀ + 2 / x₀ with hD2def
  have hD2nn : 0 ≤ D2 := by rw [hD2def]; positivity
  have hlog3gt1 : (1:ℝ) < Real.log 3 := by
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  have hloglog3pos : 0 < Real.log (Real.log 3) := Real.log_pos hlog3gt1
  set Kc : ℝ := (Real.log (Real.log 3)) ^ (-(1/2 : ℝ)) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef, Real.rpow_neg hloglog3pos.le, ← Real.sqrt_eq_rpow]
    exact inv_pos.mpr (Real.sqrt_pos.mpr hloglog3pos)
  set Pc : ℝ := D0 * (24 * cF' * D2 + 12 * Kc * Cef * (x₀ + 1 / x₀ + 1)) with hPcdef
  have hPcnn : 0 ≤ Pc := by rw [hPcdef]; positivity
  obtain ⟨L₀, hL₀one, hL₀⟩ :=
    Commons.Analysis.Asymptotics.le_mul_exp_sqrt_log_eventually
      (P := Pc * Real.exp x₀) (x₀ := x₀) (δ := 1 * (ε / 2)) (by positivity)
  refine ⟨max L₀ 5, ?_⟩
  intro f hcont hsupp hf2 hBnd hf0 hfbd
  intro N _inst χ hχ hχprim L hLth hlogNle h31 s hsre hsim
  -- ===== `f 0 = 1`: the constants of the restructured argument are those for `f 0 = 1` =====
  have hf0pos : (0:ℝ) < f 0 := by rw [hf0]; norm_num
  have hD0def' : D0 = B + 2 * (B * x₀ + |f 0| / x₀) + (B * x₀ ^ 2 + |f 0|) + 1 := by
    rw [hD0def, hf0, abs_one]
  have hD2def' : D2 = 3 * x₀ + 2 * |f 0| / x₀ := by rw [hD2def, hf0, abs_one]; ring
  have hPcdef' : Pc = D0 * (24 * cF' * D2 + 12 * Kc * Cef * (x₀ + |f 0| / x₀ + 1)) := by
    rw [hPcdef, hf0, abs_one]

  have hL₀le : L₀ ≤ L := le_trans (le_max_left _ _) hLth
  have hL5 : 5 ≤ L := le_trans (le_max_right _ _) hLth
  have hLgt1 : 1 < L := by linarith only [hL5]
  have hL1 : 1 ≤ L := by linarith only [hL5]
  have hLpos : 0 < L := by linarith only [hL5]
  have hlogL1 : 1 ≤ Real.log L := by
    have h5 : (1:ℝ) ≤ Real.log 5 := by
      have h := Real.log_le_log (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_three, hδ0, hδ1] : Real.exp 1 ≤ 5)
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 5) hL5
    linarith only [h5, h]
  have hlogLnn : 0 ≤ Real.log L := by linarith only [hlogL1]
  have hlogLpos : 0 < Real.log L := by linarith only [hlogL1]
  have hlog3leL : Real.log 3 ≤ L := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith only [h, hL5]
  have habsorb : Pc * Real.exp (x₀ * (Real.sqrt (Real.log L) + 1)) * (1 + Real.log L) ^ 5
      ≤ f 0 * (ε / 2) * L := by
    have h := hL₀ L hL₀le
    have he : Pc * Real.exp (x₀ * (Real.sqrt (Real.log L) + 1)) * (1 + Real.log L) ^ 5
        = (Pc * Real.exp x₀) * Real.exp (x₀ * Real.sqrt (Real.log L)) * (1 + Real.log L) ^ 5 := by
      rw [show Real.exp (x₀ * (Real.sqrt (Real.log L) + 1))
            = Real.exp x₀ * Real.exp (x₀ * Real.sqrt (Real.log L)) by
          rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [he, hf0]
    simpa using h
  have hsr : |s.re - 1| ≤ Real.sqrt (Real.log L) / L := hsre
  have hsimL : |s.im| ≤ 10 * L := hsim
  -- ===== the shifted point and shifted weight =====
  set η : ℝ := 1 / (L * Real.log L) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hηle : η ≤ Real.sqrt (Real.log L) / L := by
    rw [hηdef, show 1 / (L * Real.log L) = (1 / Real.log L) / L by field_simp]
    rw [div_le_div_iff_of_pos_right hLpos, div_le_iff₀ hlogLpos]
    have hs1 : (1:ℝ) ≤ Real.sqrt (Real.log L) := Real.one_le_sqrt.mpr hlogL1
    have hs2 : (Real.sqrt (Real.log L)) ^ 2 = Real.log L := Real.sq_sqrt hlogLnn
    nlinarith only [hs1, hs2]
  have hη_le_logL : η ≤ Real.log L / L := by
    rw [hηdef, show 1 / (L * Real.log L) = (1 / Real.log L) / L by field_simp]
    rw [div_le_div_iff_of_pos_right hLpos, div_le_iff₀ hlogLpos]
    nlinarith only [hlogL1]
  set β : ℝ := (1 + η) - s.re with hβdef
  set sp : ℂ := ((1 + η : ℝ) : ℂ) + (s.im : ℂ) * Complex.I with hspdef
  have hsp_eq : s + (β : ℂ) = sp := by
    rw [hspdef, hβdef]
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, sub_zero, add_zero] <;> ring
  set α : ℝ := β * L with hαdef
  have hβabs : |β| ≤ Real.sqrt (Real.log L) / L + η := by
    rw [hβdef]
    have h1 : (1 + η) - s.re = (1 - s.re) + η := by ring
    rw [h1]
    calc |(1 - s.re) + η| ≤ |1 - s.re| + |η| := abs_add_le _ _
      _ = |s.re - 1| + η := by rw [abs_sub_comm, abs_of_pos hηpos]
      _ ≤ Real.sqrt (Real.log L) / L + η := by linarith only [hsr]
  have hαabs : |α| ≤ Real.sqrt (Real.log L) + 1 := by
    rw [hαdef, abs_mul, abs_of_pos hLpos]
    have h := mul_le_mul_of_nonneg_right hβabs hLpos.le
    have h2 : (Real.sqrt (Real.log L) / L + η) * L = Real.sqrt (Real.log L) + 1 / Real.log L := by
      rw [hηdef]; field_simp
    have h4 : 1 / Real.log L ≤ 1 := by
      rw [div_le_one hlogLpos]; linarith only [hlogL1]
    rw [h2] at h
    linarith only [h, h4]
  set g : ℝ → ℝ := fun τ => Real.exp (α * τ) * f τ with hgdef
  have hg0 : g 0 = f 0 := by simp [hgdef]
  have hcont_g : ContinuousOn g (Set.Ici 0) := by
    rw [hgdef]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hcont
  have hsupp_g : ∀ τ : ℝ, x₀ ≤ τ → g τ = 0 := by
    intro τ hτ
    rw [hgdef]
    dsimp only
    rw [hsupp τ hτ, mul_zero]
  obtain ⟨hf2_g, hBnd_g⟩ :=
    Commons.Analysis.Calculus.norm_iteratedDeriv_two_exp_mul_real_le (x₀ := x₀) (B := B) (α := α) hx₀ hcont hsupp hf2 hBnd
  have hf2_g' : ContDiffOn ℝ 2 g (Set.Ioo 0 x₀) := by rw [hgdef]; exact hf2_g
  set Bg : ℝ := Real.exp (|α| * x₀) * (B + 2 * |α| * (B * x₀ + |f 0| / x₀) + |α| ^ 2 * (B * x₀ ^ 2 + |f 0|)) with hBgdef
  have hBgnn : 0 ≤ Bg := by rw [hBgdef]; positivity
  have hBnd_gg : ∀ τ ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 g τ‖ ≤ Bg := by
    intro τ hτ
    rw [hBgdef]
    have h := hBnd_g τ hτ
    simpa only [hgdef] using h
  have hsp_re : sp.re = 1 + η := by simp [hspdef]
  have hsp_im : sp.im = s.im := by simp [hspdef]
  have hsp_norm : ‖sp‖ ≤ 2 + 10 * L := by
    have h1 : ‖sp‖ ≤ |sp.re| + |sp.im| := Complex.norm_le_abs_re_add_abs_im sp
    rw [hsp_re, hsp_im] at h1
    have h2 : |1 + η| = 1 + η := abs_of_pos (by linarith only [hηpos])
    rw [h2] at h1
    have h3 : η ≤ 1 := by
      rw [hηdef, div_le_one (by positivity : (0:ℝ) < L * Real.log L)]
      nlinarith only [hL1, hlogL1]
    linarith only [h1, h3, hsimL]
  have hLs : DirichletCharacter.LFunction χ sp ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hsp_re]; linarith only [hηpos])
  have hsr' : |sp.re - 1| ≤ Real.sqrt (Real.log L) / L := by
    rw [hsp_re, show 1 + η - 1 = η by ring, abs_of_pos hηpos]
    exact hηle
  -- ===== the explicit formula at the shifted point =====
  set Eef : ℝ := Cef * (Bg * x₀ + |f 0| / x₀ + 1) * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖sp‖) with hEefdef
  set Tg : ℂ := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ sp *
      ((g (Real.log n / L) : ℝ) : ℂ) with hTgdef
  set I : ℂ → ℂ := fun u => ∫ τ in (0:ℝ)..x₀,
      Complex.exp (-(((s - u) * (L : ℂ)) * (τ : ℂ))) * ((f τ : ℝ) : ℂ) with hIdef
  set F0 : ℂ → ℂ := fun u =>
      (∫ τ in (0:ℝ)..x₀, Complex.exp (-(((sp - u) * (L : ℂ)) * (τ : ℂ))) * ((g τ : ℝ) : ℂ))
        - ((g 0 : ℝ) : ℂ) / ((sp - u) * (L : ℂ)) with hF0def
  set Sz : ℂ := ∑' u : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ) : ℂ) * F0 u with hSzdef
  have hkey : ‖Tg + L * Sz + ((g 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) sp‖ ≤ Eef := by
    rw [hTgdef, hSzdef, hEefdef]
    simpa [hF0def, hg0] using
      (hEF Bg hBgnn χ hχ hχprim hcont_g hsupp_g hf2_g' hBnd_gg hLgt1 sp hsr' hLs)
  have hkey_re : Tg.re + L * Sz.re + g 0 * (logDeriv (DirichletCharacter.LFunction χ) sp).re ≤ Eef := by
    have h1 : (Tg + L * Sz + ((g 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) sp).re ≤ Eef :=
      le_trans (Complex.re_le_norm _) hkey
    have h2 : (Tg + L * Sz + ((g 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) sp).re
        = Tg.re + L * Sz.re + g 0 * (logDeriv (DirichletCharacter.LFunction χ) sp).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero]
    linarith only [h1, h2.le, _inst, h2]
  have hTg_eq : Tg.re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod N) / (n : ℂ) ^ s).re) * f (Real.log n / L) := by
    rw [hTgdef]
    have hterm : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ sp * ((g (Real.log n / L) : ℝ) : ℂ)
        = (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hcp := div_cpow_mul_exp_eq β L hLpos s n hn1
        have hg' : (g (Real.log n / L) : ℂ)
            = (Real.exp (β * L * (Real.log n / L)) : ℂ) * (f (Real.log n / L) : ℂ) := by
          rw [hgdef, hαdef, Complex.ofReal_mul]
        calc (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ sp * ((g (Real.log n / L) : ℝ) : ℂ)
            = (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
                (((n : ℂ) ^ sp)⁻¹ * ((Real.exp (β * L * (Real.log n / L)) : ℝ) : ℂ)) *
                  ((f (Real.log n / L) : ℝ) : ℂ) := by
              rw [hg', div_eq_mul_inv]
              ring
          _ = (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * ((n : ℂ) ^ s)⁻¹ *
                  ((f (Real.log n / L) : ℝ) : ℂ) := by
              rw [show sp = s + (β : ℂ) from hsp_eq.symm, hcp]
          _ = (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) := by
              rw [div_eq_mul_inv]
              ring
    have h1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ sp * ((g (Real.log n / L) : ℝ) : ℂ))
        = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) :=
      tsum_congr hterm
    rw [h1]
    exact (smoothed_vonMangoldt_tsum_re hx₀ χ hsupp hLpos s).2
  -- ===== divisor data =====
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u with hDdef
  set Db : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2)) u with hDbdef
  set near : ℂ → Prop := fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ with hneardef
  set Ψ : ℂ → ℂ := fun u => ((D u : ℤ) : ℂ) * F0 u with hΨdef
  set ψ : ℂ → ℝ := fun u => (Ψ u).re with hψdef
  set ψn : ℂ → ℝ := fun u => if near u then (Ψ u).re else 0 with hψndef
  set ψf : ℂ → ℝ := fun u => if near u then 0 else (Ψ u).re with hψfdef
  have hD_eq_Db : ∀ u : ℂ, near u → D u = Db u := by
    intro u hu
    have hmem : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := near_mem_closedBall hδ1.le hu
    rw [hDdef, hDbdef]
    exact divisor_univ_eq_closedBall χ hχ hmem
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ ((D u : ℤ) : ℝ) := by
    intro u; rw [hDdef]; exact div_univ_nonneg χ hχ u
  set Ag : ℝ := 3 * Bg * x₀ + 2 * |f 0| / x₀ with hAgdef
  have hAgnn : 0 ≤ Ag := by rw [hAgdef]; positivity
  have hF0bound : ∀ u : ℂ, D u ≠ 0 → ‖F0 u‖ ≤ Ag / (L ^ 2 * ‖sp - u‖ ^ 2) := by
    intro u hu
    have hstrip := div_univ_strip χ hχ hχprim hu
    have h := norm_rdcKernel_le (x₀ := x₀) (B := Bg) hx₀ hBgnn hcont_g hsupp_g hf2_g' hBnd_gg hLpos
      (s := sp) (u := u) (by rw [hsp_re]; linarith only [hstrip.2, hηpos])
    rw [hF0def, hAgdef]
    simpa only [hg0] using h
  have hΨbound : ∀ u : ℂ, ‖Ψ u‖ ≤ (Ag / (L ^ 2 * ‖sp - u‖ ^ 2)) * ((D u : ℤ) : ℝ) := by
    intro u
    rw [hΨdef, norm_mul]
    by_cases hD : D u = 0
    · rw [hD]; simp
    · have hDabs : ‖(((D u : ℤ)) : ℂ)‖ = ((D u : ℤ) : ℝ) := by
        rw [show (((D u : ℤ)) : ℂ) = (((D u : ℤ) : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hDnn u)]
      rw [hDabs]
      calc ((D u : ℤ) : ℝ) * ‖F0 u‖ = ‖F0 u‖ * ((D u : ℤ) : ℝ) := by ring
        _ ≤ (Ag / (L ^ 2 * ‖sp - u‖ ^ 2)) * ((D u : ℤ) : ℝ) :=
            mul_le_mul_of_nonneg_right (hF0bound u hD) (hDnn u)
  -- ===== the far weight =====
  set farw : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) * (if near u then 0 else (1 / ‖sp - u‖ ^ 2)) with hfarwdef
  have hfarw_nn : ∀ u : ℂ, 0 ≤ farw u := by
    intro u
    rw [hfarwdef]
    refine mul_nonneg (hDnn u) ?_
    by_cases h : near u <;> simp [h]
  have hif_far : ∀ u : ℂ, (if near u then (0:ℝ) else (1 / ‖sp - u‖ ^ 2))
      = (if ‖(1 : ℂ) + (sp.im : ℂ) * Complex.I - u‖ > δ then (1 / ‖sp - u‖ ^ 2) else 0) := by
    intro u
    have hspim : (sp.im : ℂ) = (s.im : ℂ) := by rw [hsp_im]
    by_cases h : near u
    · have h2 : ¬ (‖(1 : ℂ) + (sp.im : ℂ) * Complex.I - u‖ > δ) := by
        rw [hspim]
        exact not_lt.mpr (by simpa only [hneardef] using h)
      rw [if_pos h, if_neg h2]
    · have h2 : ‖(1 : ℂ) + (sp.im : ℂ) * Complex.I - u‖ > δ := by
        rw [hspim]
        exact not_le.mp (by simpa only [hneardef] using h)
      rw [if_neg h, if_pos h2]
  have hfarw_summ : Summable farw := by
    refine Summable.congr ((hF χ hχ hχprim (s := sp) (by rw [hsp_re]; linarith only [hηpos]) hδ0 hδ1.le).1) (fun u => ?_)
    rw [hfarwdef]
    dsimp only
    rw [hDdef, ← hif_far u]
  have hfarw_bd : (∑' u, farw u) ≤ cF' * (L + Real.log (2 + ‖sp‖) + 2) := by
    have h := (hF χ hχ hχprim (s := sp) (by rw [hsp_re]; linarith only [hηpos]) hδ0 hδ1.le).2
    have h1 : (∑' u : ℂ, farw u) = ∑' u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (sp.im : ℂ) * Complex.I - u‖ > δ then (1 / ‖sp - u‖ ^ 2) else 0) := by
      rw [hfarwdef]
      exact tsum_congr (fun u => by rw [hDdef, ← hif_far u])
    rw [h1, hcF'def]
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · linarith only [hlogNle]
    · positivity
  -- ===== summability of the pieces =====
  have hSfin : (Function.support (fun u : ℂ => ((Db u : ℤ) : ℝ))).Finite := by
    rw [hDbdef]
    exact divisor_real_finiteSupport χ hχ 0 (|s.im| + 2)
  have hkey_S : ∀ u : ℂ, near u → D u ≠ 0 → u ∈ hSfin.toFinset := by
    intro u hnear hDne
    have hmem : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := near_mem_closedBall hδ1.le hnear
    have h1 : D u = Db u := hD_eq_Db u hnear
    have h2 : ((Db u : ℤ) : ℝ) ≠ 0 := by
      rw [← h1]
      intro h0
      exact hDne (by exact_mod_cast h0)
    exact hSfin.mem_toFinset.mpr (by rw [Function.mem_support]; exact h2)
  have hΨn_supp : Function.support (fun u : ℂ => (if near u then Ψ u else 0)) ⊆ (↑hSfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hnear : near u := by by_contra h; exact hu (by rw [if_neg h])
    have hΨne : Ψ u ≠ 0 := by by_contra h; exact hu (by rw [if_pos hnear, h])
    have hDne : D u ≠ 0 := by
      intro h0
      exact hΨne (by simp [hΨdef, h0])
    exact hkey_S u hnear hDne
  have hΨn_summ : Summable (fun u : ℂ => if near u then Ψ u else 0) :=
    summable_of_ne_finset_zero (s := hSfin.toFinset) (fun u hu => by
      by_contra hne
      exact hu (hΨn_supp (by rw [Function.mem_support]; exact hne)))
  have hΨf_pt : ∀ u : ℂ, ‖(if near u then (0:ℂ) else Ψ u)‖ ≤ (Ag / L ^ 2) * farw u := by
    intro u
    by_cases h : near u
    · rw [if_pos h]; simp only [norm_zero]
      exact mul_nonneg (div_nonneg hAgnn (by positivity)) (hfarw_nn u)
    · rw [if_neg h]
      calc ‖Ψ u‖ ≤ (Ag / (L ^ 2 * ‖sp - u‖ ^ 2)) * ((D u : ℤ) : ℝ) := hΨbound u
        _ = (Ag / L ^ 2) * farw u := by
              rw [hfarwdef]
              dsimp only
              rw [if_neg h]
              ring
  have hΨf_summ : Summable (fun u : ℂ => if near u then (0:ℂ) else Ψ u) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun u => norm_nonneg _) hΨf_pt ?_
    exact hfarw_summ.mul_left _
  have hΨsumm : Summable Ψ := by
    have h1 : Summable (fun u : ℂ => (if near u then Ψ u else 0) + (if near u then 0 else Ψ u)) :=
      hΨn_summ.add hΨf_summ
    refine Summable.congr h1 (fun u => ?_)
    by_cases h : near u <;> simp [h]
  have hψn_abs : ∀ u : ℂ, ‖ψn u‖ ≤ ‖(if near u then Ψ u else 0)‖ := by
    intro u
    by_cases h : near u
    · have h1 : ‖ψn u‖ = |(Ψ u).re| := by rw [hψndef]; simp [h]
      have h2 : ‖(if near u then Ψ u else 0)‖ = ‖Ψ u‖ := by rw [if_pos h]
      rw [h1, h2]
      exact Complex.abs_re_le_norm _
    · have h1 : ‖ψn u‖ = 0 := by rw [hψndef]; simp [h]
      rw [h1]
      exact norm_nonneg _
  have hψn_summ : Summable ψn := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun u => norm_nonneg _) hψn_abs (hΨn_summ.norm)
  have hψf_abs0 : ∀ u : ℂ, ‖ψf u‖ ≤ ‖(if near u then (0:ℂ) else Ψ u)‖ := by
    intro u
    by_cases h : near u
    · have h1 : ‖ψf u‖ = 0 := by rw [hψfdef]; simp [h]
      rw [h1]
      exact norm_nonneg _
    · have h1 : ‖ψf u‖ = |(Ψ u).re| := by rw [hψfdef]; simp [h]
      have h2 : ‖(if near u then (0:ℂ) else Ψ u)‖ = ‖Ψ u‖ := by rw [if_neg h]
      rw [h1, h2]
      exact Complex.abs_re_le_norm _
  have hψf_summ : Summable ψf := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun u => norm_nonneg _) hψf_abs0 (hΨf_summ.norm)
  have hψ_summ : Summable ψ := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun u => norm_nonneg _) (fun u => ?_) (hΨsumm.norm)
    have h1 : ‖ψ u‖ = |(Ψ u).re| := by rw [hψdef]; simp
    rw [h1]
    exact Complex.abs_re_le_norm _
  have hψ_split : ∑' u, ψ u = ∑' u, ψn u + ∑' u, ψf u := by
    rw [← Summable.tsum_add hψn_summ hψf_summ]
    exact tsum_congr (fun u => by
      rw [hψdef, hψndef, hψfdef]
      by_cases h : near u <;> simp [h])
  have hSz_re : Sz.re = ∑' u, ψ u := by
    rw [hSzdef, hΨdef]
    rw [Complex.re_tsum hΨsumm]
  -- ===== pointwise identity for the near terms =====
  have hψn_pt : ∀ u : ℂ, (Ψ u).re
      = ((D u : ℤ) : ℝ) * ((I u).re - (f 0 / L) * ((1 / (sp - u)).re)) := by
    intro u
    have h1 : (∫ τ in (0:ℝ)..x₀, Complex.exp (-(((sp - u) * (L : ℂ)) * (τ : ℂ))) * ((g τ : ℝ) : ℂ)) = I u := by
      have h0 := integral_shift_eq β L x₀ s u f
      rw [hIdef, ← hsp_eq]
      simpa only [hgdef, hαdef] using h0
    have hF0u : F0 u = (∫ τ in (0:ℝ)..x₀, Complex.exp (-(((sp - u) * (L : ℂ)) * (τ : ℂ))) * ((g τ : ℝ) : ℂ))
        - ((g 0 : ℝ) : ℂ) / ((sp - u) * (L : ℂ)) := by rw [hF0def]
    have hΨu : Ψ u = ((D u : ℤ) : ℂ) * F0 u := by rw [hΨdef]
    have h2 : Ψ u = ((D u : ℤ) : ℂ) * (I u - ((g 0 : ℝ) : ℂ) / ((sp - u) * (L : ℂ))) := by
      rw [hΨu, hF0u, h1]
    rw [h2]
    have h3 : (((D u : ℤ)) : ℂ) * (I u - ((g 0 : ℝ) : ℂ) / ((sp - u) * (L : ℂ)))
        = (((D u : ℤ) : ℝ) : ℂ) * (I u - (((f 0 / L : ℝ)) : ℂ) * ((sp - u)⁻¹)) := by
      rw [hg0, div_eq_mul_inv, div_eq_mul_inv]
      push_cast
      rw [mul_inv_rev]
      ring
    have h4 : ∀ (a b : ℝ) (z w : ℂ),
        (((a : ℂ) * (z - (b : ℂ) * w⁻¹)).re) = a * (z.re - b * (1 / w).re) := by
      intro a b z w
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero, one_div]
    rw [h3]
    exact h4 ((D u : ℤ) : ℝ) (f 0 / L) (I u) (sp - u)
  -- ===== the near part as an explicit finsum =====
  have hψn_eq : ∑' u : ℂ, ψn u
      = ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0)
        - (f 0 / L) * ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0) := by
    have hpt : ∀ u : ℂ, ψn u = ((D u : ℤ) : ℝ) *
        (if near u then ((I u).re - (f 0 / L) * ((1 / (sp - u)).re)) else 0) := by
      intro u
      by_cases h : near u
      · have h1 : ψn u = (Ψ u).re := by rw [hψndef]; simp [h]
        rw [h1, hψn_pt u, if_pos h]
      · have h1 : ψn u = 0 := by rw [hψndef]; simp [h]
        rw [h1, if_neg h, mul_zero]
    have hstep : ∑' u : ℂ, ψn u = ∑' u : ℂ, ((D u : ℤ) : ℝ) *
        (if near u then ((I u).re - (f 0 / L) * ((1 / (sp - u)).re)) else 0) := tsum_congr hpt
    have hsupp1 : Function.support (fun u : ℂ => ((D u : ℤ) : ℝ) *
        (if near u then ((I u).re - (f 0 / L) * ((1 / (sp - u)).re)) else 0))
        ⊆ (↑hSfin.toFinset : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hnear : near u := by by_contra h; exact hu (by rw [if_neg h, mul_zero])
      have hDne : D u ≠ 0 := by intro h0; exact hu (by rw [if_pos hnear, h0]; simp)
      exact hkey_S u hnear hDne
    have hsupp2 : Function.support (fun u : ℂ => ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0))
        ⊆ (↑hSfin.toFinset : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hnear : near u := by by_contra h; exact hu (by rw [if_neg h, mul_zero])
      have hDne : D u ≠ 0 := by intro h0; exact hu (by rw [if_pos hnear, h0]; simp)
      exact hkey_S u hnear hDne
    have hsupp3 : Function.support (fun u : ℂ => ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
        ⊆ (↑hSfin.toFinset : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hnear : near u := by by_contra h; exact hu (by rw [if_neg h, mul_zero])
      have hDne : D u ≠ 0 := by intro h0; exact hu (by rw [if_pos hnear, h0]; simp)
      exact hkey_S u hnear hDne
    rw [hstep, tsum_eq_sum (s := hSfin.toFinset) (fun u hu => by
          by_contra hne
          exact hu (hsupp1 (by rw [Function.mem_support]; exact hne))),
        finsum_eq_sum_of_support_subset _ hsupp2, finsum_eq_sum_of_support_subset _ hsupp3,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    by_cases h : near u <;> simp [h] <;> ring
  -- ===== the hypothesis, at the shifted point =====
  have h31' : -(logDeriv (DirichletCharacter.LFunction χ) sp).re
      + (∑ᶠ u : ℂ, ((Db u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
      ≤ ((1/6 : ℝ) + ε / 2) * L := by
    have hge : 1 + 1 / (L * Real.log L) ≤ sp.re := by
      rw [hsp_re, hηdef]
    have hle : sp.re ≤ 1 + Real.log L / L := by
      rw [hsp_re]
      linarith only [hη_le_logL]
    have him : |sp.im| ≤ 10 * L := by rw [hsp_im]; exact hsim
    have h := h31 sp hge hle him
    rw [hsp_im] at h
    simpa only [hDbdef, hneardef, Complex.neg_re] using h
  -- ===== the far part =====
  have hψf_bd : |∑' u : ℂ, ψf u| ≤ (Ag / L ^ 2) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)) := by
    have hpt : ∀ u : ℂ, |ψf u| ≤ (Ag / L ^ 2) * farw u := fun u => by
      have h1 : ‖ψf u‖ ≤ ‖(if near u then (0:ℂ) else Ψ u)‖ := hψf_abs0 u
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (hΨf_pt u)
    have h1 : |∑' u : ℂ, ψf u| ≤ ∑' u : ℂ, |ψf u| := by
      have h3 := norm_tsum_le_tsum_norm hψf_summ.norm
      simpa only [Real.norm_eq_abs] using h3
    have h2 : ∑' u : ℂ, |ψf u| ≤ ∑' u : ℂ, (Ag / L ^ 2) * farw u :=
      Summable.tsum_le_tsum hpt (hψf_summ.norm) (hfarw_summ.mul_left _)
    rw [tsum_mul_left] at h2
    have h4 : (0:ℝ) ≤ Ag / L ^ 2 := div_nonneg hAgnn (by positivity)
    have h5 := mul_le_mul_of_nonneg_left hfarw_bd h4
    linarith only [h1, h2, h5]
  -- ===== the numeric absorption =====
  set E0 : ℝ := Real.exp (x₀ * Real.sqrt (Real.log L)) * (1 + Real.log L) * D0 with hE0def
  have hnum : (Ag / L) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)) + Eef ≤ f 0 * (ε / 2) * L := by
    have hcore := numeric_core_wide (x₀ := x₀) (B := B) (f0 := f 0) (ε := ε) (L := L) (α := α)
      (spn := ‖sp‖) (Bg := Bg) (Ag := Ag) (Cef := Cef) (cF := cF') (D0 := D0) (D2 := D2)
      (Kc := Kc) (Pc := Pc) hx₀ hB hf0pos hε hL5 hαabs hsp_norm (norm_nonneg sp)
      hCefpos hcF'pos hBgdef hAgdef hD0def' hD2def' hKcdef hPcdef' habsorb
    simpa only [hAgdef, hBgdef, hEefdef] using hcore
  -- ===== final assembly =====
  have hnear_D_eq_Db_I : (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0))
      = ∑ᶠ u : ℂ, ((Db u : ℤ) : ℝ) * (if near u then (I u).re else 0) := by
    refine finsum_congr (fun u => ?_)
    by_cases h : near u
    · rw [if_pos h, hD_eq_Db u h]
    · simp [h]
  have hstep1 : Tg.re ≤ -L * (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0))
      + f 0 * (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
      - f 0 * (logDeriv (DirichletCharacter.LFunction χ) sp).re
      + ((Ag / L) * (cF' * (L + Real.log (2 + ‖sp‖) + 2))) + Eef := by
    have h1 := hkey_re
    have h2 : L * Sz.re = L * (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0))
        - f 0 * (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
        + L * (∑' u : ℂ, ψf u) := by
      rw [hSz_re, hψ_split, hψn_eq]
      field_simp
    rw [h2, hg0] at h1
    have h3 : -(L * (∑' u : ℂ, ψf u))
        ≤ (Ag / L) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)) := by
      have h4 : -(∑' u : ℂ, ψf u) ≤ (Ag / L ^ 2) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)) :=
        le_trans (neg_le_abs _) hψf_bd
      have h5 : L * (-(∑' u : ℂ, ψf u))
          ≤ L * ((Ag / L ^ 2) * (cF' * (L + Real.log (2 + ‖sp‖) + 2))) :=
        mul_le_mul_of_nonneg_left h4 hLpos.le
      have h6 : L * ((Ag / L ^ 2) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)))
          = (Ag / L) * (cF' * (L + Real.log (2 + ‖sp‖) + 2)) := by
        field_simp
      have h7 : -(L * (∑' u : ℂ, ψf u)) = L * (-(∑' u : ℂ, ψf u)) := by ring
      linarith only [h5, h6.le, h6.ge, h7]
    linarith only [h1, h3]
  have hstep2 : Tg.re ≤ -L * (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then (I u).re else 0))
      + f 0 * ((1/6 : ℝ) + ε/2) * L
      + ((Ag / L) * (cF' * (L + Real.log (2 + ‖sp‖) + 2))) + Eef := by
    have h1 := hstep1
    have hDb_eq : (∑ᶠ u : ℂ, ((Db u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
        = ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0) := by
      refine finsum_congr (fun u => ?_)
      by_cases h : near u
      · rw [if_pos h, hD_eq_Db u h]
      · simp [h]
    have h3 : (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
        - (logDeriv (DirichletCharacter.LFunction χ) sp).re ≤ ((1/6 : ℝ) + ε/2) * L := by
      rw [← hDb_eq]
      have h4 : -(logDeriv (DirichletCharacter.LFunction χ) sp).re
          + (∑ᶠ u : ℂ, ((Db u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
          ≤ ((1/6 : ℝ) + ε/2) * L := h31'
      rw [sub_eq_add_neg, add_comm]
      exact h4
    have h2 : f 0 * ((∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * (if near u then ((1 / (sp - u)).re) else 0))
        - (logDeriv (DirichletCharacter.LFunction χ) sp).re) ≤ f 0 * (((1/6 : ℝ) + ε/2) * L) :=
      mul_le_mul_of_nonneg_left h3 hf0pos.le
    linarith only [h1, h2]
  have hfinal : Tg.re ≤ -L * (∑ᶠ u : ℂ, ((Db u : ℤ) : ℝ) * (if near u then (I u).re else 0))
      + f 0 * ((1/6 : ℝ) + ε) * L := by
    have h1 := hstep2
    have h2 := hnum
    rw [hnear_D_eq_Db_I] at h1
    linarith only [h1, h2]
  have hgoal : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod N) / (n : ℂ) ^ s).re) * f (Real.log n / L))
      ≤ -L * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
      + f 0 * ((1/6 : ℝ) + ε) * L := by
    rw [← hTg_eq]
    simpa only [hDbdef, hneardef, hIdef] using hfinal
  exact hgoal

end Work.LinnikAreas.A5
