import Mathlib

namespace Work.RHContract.B

open MeasureTheory Complex
open scoped Topology

/-!
# Analyticity of the truncated Mellin-type integral `∫_1^{x₀} g x · x^{-s-1} dx`

The function `s ↦ ∫_1^{x₀} g x · x^{-s-1} dx`, with `g` merely integrable on `(1, x₀]`, is
complex differentiable.  This is differentiation under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the parameter space
`ℂ`: for each `x > 1` the integrand is entire in `s` with derivative
`(g x) · x^{-s-1} · log x · (-1)`, and on the compact interval `[1, x₀]` both the integrand and
its `s`-derivative are bounded by a constant multiple of `|g|`.
-/

/-- For `t ≥ 1` and `p` in the unit ball around `q`, the complex power `t ^ (-p - 1)` is bounded
uniformly by `x ^ ‖q‖` whenever `t ≤ x`.  The exponent `-p.re - 1` is at most `‖q‖`
because `p` is close to `q`. -/
private lemma cpow_neg_sub_one_norm_le {t x : ℝ} (ht1 : 1 ≤ t) (htx : t ≤ x) {p q : ℂ}
    (hp : p ∈ Metric.ball q 1) : ‖(t : ℂ) ^ (-p - 1)‖ ≤ x ^ ‖q‖ := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  have hre : (-p - 1).re = -p.re - 1 := by simp
  rw [hre]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le ht1 ?_)
    (Real.rpow_le_rpow (by linarith) htx (norm_nonneg _))
  have h1 : ‖p - q‖ < 1 := by rw [Metric.mem_ball, dist_eq_norm] at hp; exact hp
  have h2 : -p.re ≤ |p.re| := neg_le_abs _
  have h2' : |p.re| ≤ ‖p‖ := Complex.abs_re_le_norm p
  have h3 : ‖p‖ ≤ ‖q‖ + ‖p - q‖ := by
    calc ‖p‖ = ‖(p - q) + q‖ := by ring_nf
      _ ≤ ‖p - q‖ + ‖q‖ := norm_add_le _ _
      _ = ‖q‖ + ‖p - q‖ := by ring
  linarith

/-- For `1 ≤ t ≤ x`, the complex logarithm of `t` is bounded in norm by `|log x|`. -/
private lemma log_norm_le {t x : ℝ} (ht1 : 1 ≤ t) (htx : t ≤ x) :
    ‖Complex.log (t : ℂ)‖ ≤ |Real.log x| := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hval : ‖(((Real.log t : ℝ)) : ℂ)‖ = |Real.log t| := by simp
  rw [← Complex.ofReal_log ht0.le, hval, abs_le]
  exact ⟨by have h : 0 ≤ Real.log t := Real.log_nonneg ht1; linarith [abs_nonneg (Real.log x)],
         by have h : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx; linarith [le_abs_self (Real.log x)]⟩

/-- The derivative of the integrand with respect to the exponent `s`. -/
private lemma integrand_hasDerivAt (g : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℂ) :
    HasDerivAt (fun w : ℂ => (g t : ℂ) * (t : ℂ) ^ (-w - 1))
      ((g t : ℂ) * ((t : ℂ) ^ (-s - 1) * Complex.log (t : ℂ) * (-1))) s := by
  have h1 : HasDerivAt (fun w : ℂ => -w - 1) (-1) s := (hasDerivAt_id s).neg.sub_const 1
  have h2 : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (-w - 1))
      ((t : ℂ) ^ (-s - 1) * Complex.log (t : ℂ) * (-1)) s := by
    have := h1.const_cpow (c := (t : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr ht))
    simpa using this
  simpa using h2.const_mul (g t : ℂ)

theorem head_analytic
    (g : ℝ → ℝ) (x₀ : ℝ) (hx₀ : 1 ≤ x₀)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioc 1 x₀)) :
    Differentiable ℂ (fun s : ℂ => ∫ x in (1 : ℝ)..x₀, (g x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
  intro s₀
  have huIoc : Set.uIoc 1 x₀ = Set.Ioc 1 x₀ := Set.uIoc_of_le hx₀
  set C : ℝ := x₀ ^ ‖s₀‖ * |Real.log x₀| with hCdef
  have hgs0 : s₀ ∈ Metric.ball s₀ (1 : ℝ) := Metric.mem_ball_self zero_lt_one
  have hgA : AEMeasurable g (volume.restrict (Set.Ioc 1 x₀)) := by
    have h := hg; rw [IntegrableOn] at h; exact h.aemeasurable
  have hgI : Integrable g (volume.restrict (Set.Ioc 1 x₀)) := hg
  refine ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => (g x : ℂ) * (x : ℂ) ^ (-s - 1))
    (F' := fun s x => (g x : ℂ) * ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1)))
    (a := 1) (b := x₀) (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := fun t => C * ‖g t‖)
    (Metric.isOpen_ball.mem_nhds hgs0) ?_ ?_ ?_ ?_ ?_ ?_).2).differentiableAt
  · refine Filter.Eventually.of_forall (fun p => ?_)
    rw [huIoc]
    exact ((Complex.measurable_ofReal.comp_aemeasurable hgA).mul
      ((by fun_prop : Measurable (fun x : ℝ => (x : ℂ) ^ (-p - 1))).aemeasurable)).aestronglyMeasurable
  · rw [intervalIntegrable_iff, huIoc]
    refine Integrable.mono' (hgI.norm.const_mul (x₀ ^ ‖s₀‖)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp_aemeasurable hgA).mul
        ((by fun_prop : Measurable (fun x : ℝ => (x : ℂ) ^ (-s₀ - 1))).aemeasurable)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [norm_mul]
      have hnorm : ‖(g x : ℂ)‖ = ‖g x‖ := by simp
      rw [hnorm]
      have hb := cpow_neg_sub_one_norm_le (le_of_lt hx.1) hx.2 hgs0
      calc ‖g x‖ * ‖(x : ℂ) ^ (-s₀ - 1)‖ ≤ ‖g x‖ * x₀ ^ ‖s₀‖ :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = x₀ ^ ‖s₀‖ * ‖g x‖ := by ring
  · rw [huIoc]
    exact ((Complex.measurable_ofReal.comp_aemeasurable hgA).mul
      ((by fun_prop : Measurable (fun x : ℝ => (x : ℂ) ^ (-s₀ - 1) * Complex.log (x : ℂ) * (-1))).aemeasurable)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t ht p hp => ?_)
    rw [huIoc] at ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
    have hkey : ‖(t : ℂ) ^ (-p - 1) * Complex.log (t : ℂ) * (-1)‖
        = ‖(t : ℂ) ^ (-p - 1)‖ * ‖Complex.log (t : ℂ)‖ := by
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one]
    rw [norm_mul, hkey]
    have hnorm : ‖(g t : ℂ)‖ = ‖g t‖ := by simp
    rw [hnorm]
    have hb := cpow_neg_sub_one_norm_le ht1 ht.2 hp
    have hl := log_norm_le ht1 ht.2
    calc ‖g t‖ * (‖(t : ℂ) ^ (-p - 1)‖ * ‖Complex.log (t : ℂ)‖)
        ≤ ‖g t‖ * (x₀ ^ ‖s₀‖ * |Real.log x₀|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb hl (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = C * ‖g t‖ := by rw [hCdef]; ring
  · rw [intervalIntegrable_iff, huIoc]
    exact hgI.norm.const_mul C
  · refine Filter.Eventually.of_forall (fun t ht p hp => ?_)
    rw [huIoc] at ht
    exact integrand_hasDerivAt g (ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)) p

end Work.RHContract.B
