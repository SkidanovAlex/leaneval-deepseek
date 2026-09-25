import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound

open MeasureTheory Set Filter
open scoped Topology

namespace Commons.Analysis.Real

noncomputable section

/-- The integrand `(ψ t − t)·((log t + 1)/(t²(log t)²))` is (Borel) measurable. -/
private lemma measurable_chebyshevPsi_sub_id_mul_psiKfun :
    Measurable (fun t : ℝ => (Chebyshev.psi t - t) *
      ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) := by
  apply Measurable.mul
  · exact Chebyshev.psi_mono.measurable.sub measurable_id
  · apply Measurable.div
    · exact Real.measurable_log.add measurable_const
    · apply Measurable.mul
      · exact measurable_id.pow_const 2
      · exact Real.measurable_log.pow_const 2

/-- Eventually `(log t)^9 ≤ t^(1/4)`: the logarithm grows slower than any positive power. -/
private lemma eventually_log_pow_nine_le_rpow_quarter :
    ∀ᶠ t : ℝ in Filter.atTop, (Real.log t) ^ 9 ≤ t ^ (1/4 : ℝ) := by
  have h1 : (fun t : ℝ => Real.log t ^ (9:ℝ)) =o[Filter.atTop]
      (fun t : ℝ => t ^ (1/4:ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (s := (1/4:ℝ)) 9 (by norm_num)
  have h2 : ∀ᶠ t : ℝ in Filter.atTop, ‖Real.log t ^ (9:ℝ)‖ ≤ ‖t ^ (1/4:ℝ)‖ :=
    h1.eventuallyLE
  filter_upwards [h2, eventually_ge_atTop (1:ℝ)] with t ht ht1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
  rw [abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg ht1) 9),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at ht
  rwa [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast] at ht

/-- Pointwise domination of the integrand by `2C·t^(−5/4)` for `t` large enough. -/
private lemma norm_integrand_le (C t : ℝ) (hC : 0 ≤ C) (htpos : 0 < t)
    (hlog1 : 1 ≤ Real.log t)
    (hpsi : |Chebyshev.psi t - t| ≤ C * Real.sqrt t * (Real.log t)^10)
    (hlb : (Real.log t)^9 ≤ t ^ (1/4:ℝ)) :
    ‖(Chebyshev.psi t - t) * ((Real.log t + 1)/(t^2 * (Real.log t)^2))‖ ≤
      2*C*t^(-5/4:ℝ) := by
  have hlogpos : 0 < Real.log t := lt_of_lt_of_le one_pos hlog1
  have hden : 0 < t^2 * (Real.log t)^2 := by positivity
  have habs : |(Real.log t + 1)/(t^2 * (Real.log t)^2)| =
      (Real.log t + 1)/(t^2 * (Real.log t)^2) := by
    apply abs_of_nonneg
    apply div_nonneg _ (le_of_lt hden)
    linarith
  have hfrac : (Real.log t + 1)/(t^2 * (Real.log t)^2) ≤ 2/(t^2 * Real.log t) := by
    have hnum : Real.log t + 1 ≤ 2 * Real.log t := by linarith
    calc (Real.log t + 1)/(t^2 * (Real.log t)^2)
        ≤ (2 * Real.log t)/(t^2 * (Real.log t)^2) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = 2/(t^2 * Real.log t) := by
          field_simp
  have hsqr : Real.sqrt t * (Real.log t)^9 / t^2 ≤ t^(-5/4:ℝ) := by
    have ht2pos : 0 < t^2 := by positivity
    calc Real.sqrt t * (Real.log t)^9 / t^2
        ≤ Real.sqrt t * t^(1/4:ℝ) / t^2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt ht2pos)
          exact mul_le_mul_of_nonneg_left hlb (Real.sqrt_nonneg t)
      _ = t^(-5/4:ℝ) := by
          rw [Real.sqrt_eq_rpow]
          have ht2 : t ^ 2 = t ^ (2:ℝ) := by
            rw [← Real.rpow_natCast t 2]
            norm_num
          rw [ht2]
          rw [← Real.rpow_add htpos, ← Real.rpow_sub htpos]
          norm_num
  calc ‖(Chebyshev.psi t - t) * ((Real.log t + 1)/(t^2 * (Real.log t)^2))‖
      = |Chebyshev.psi t - t| * |(Real.log t + 1)/(t^2 * (Real.log t)^2)| := by
        rw [Real.norm_eq_abs, abs_mul]
    _ = |Chebyshev.psi t - t| * ((Real.log t + 1)/(t^2 * (Real.log t)^2)) := by rw [habs]
    _ ≤ (C * Real.sqrt t * (Real.log t)^10) * ((Real.log t + 1)/(t^2 * (Real.log t)^2)) := by
        apply mul_le_mul_of_nonneg_right hpsi
        exact le_of_lt (div_pos (by linarith) hden)
    _ ≤ (C * Real.sqrt t * (Real.log t)^10) * (2/(t^2 * Real.log t)) := by
        apply mul_le_mul_of_nonneg_left hfrac
        positivity
    _ = 2*C*(Real.sqrt t * (Real.log t)^9 / t^2) := by
        field_simp
    _ ≤ 2*C*t^(-5/4:ℝ) := by
        apply mul_le_mul_of_nonneg_left hsqr
        linarith

theorem integrableOn_chebyshevPsi_sub_id_mul_psiKfun (h : RiemannHypothesis) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      MeasureTheory.IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi x) := by
  obtain ⟨C, hCpos, x₁, hpsi⟩ :=
    Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound h
  have hev : ∀ᶠ t : ℝ in Filter.atTop,
      x₁ ≤ t ∧ Real.exp 1 ≤ t ∧ (Real.log t)^9 ≤ t^(1/4:ℝ) := by
    filter_upwards [eventually_ge_atTop x₁, eventually_ge_atTop (Real.exp 1),
      eventually_log_pow_nine_le_rpow_quarter] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rw [Filter.eventually_atTop] at hev
  obtain ⟨x₂, hx₂⟩ := hev
  refine ⟨x₂, ?_⟩
  intro x hx
  obtain ⟨hx₁, hexp, hlb⟩ := hx₂ x hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hexp
  apply Integrable.mono' (g := fun t : ℝ => 2*C*t^(-5/4:ℝ))
  · have hg : Integrable (fun t : ℝ => t ^ (-5/4:ℝ)) (volume.restrict (Set.Ioi x)) :=
      integrableOn_Ioi_rpow_of_lt (a := (-5/4:ℝ)) (c := x) (by norm_num) hxpos
    exact hg.const_mul (2*C)
  · exact measurable_chebyshevPsi_sub_id_mul_psiKfun.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t ht
    have hxt : x₂ ≤ t := le_of_lt (lt_of_le_of_lt hx ht)
    obtain ⟨ht₁, htexp, htlb⟩ := hx₂ t hxt
    have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) htexp
    have hlog1 : 1 ≤ Real.log t := (Real.le_log_iff_exp_le htpos).mpr htexp
    exact norm_integrand_le C t (le_of_lt hCpos) htpos hlog1 (hpsi t ht₁) htlb

end

end Commons.Analysis.Real
