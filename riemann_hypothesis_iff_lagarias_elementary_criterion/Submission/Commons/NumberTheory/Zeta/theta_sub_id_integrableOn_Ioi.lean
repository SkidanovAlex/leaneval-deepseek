import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.Analysis.Real.integrableOn_log10_div_sqrt

open MeasureTheory Set Filter

namespace Commons.NumberTheory.Zeta

private lemma sqrt_div_mul_self {t : ℝ} (ht : 0 < t) :
    Real.sqrt t / (t * t) = 1 / (t * Real.sqrt t) := by
  have ht2 : t * t ≠ 0 := by positivity
  have hden : t * Real.sqrt t ≠ 0 := by positivity
  field_simp [ht.ne', ht2, hden]
  exact Real.sq_sqrt (le_of_lt ht)

private lemma theta_bound_algebra {C t : ℝ} (ht : 0 < t) :
    C * Real.sqrt t * (Real.log t) ^ 10 / (t * t) =
      C * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
  calc
    C * Real.sqrt t * (Real.log t) ^ 10 / (t * t)
        = C * ((Real.sqrt t * (Real.log t) ^ 10) / (t * t)) := by ring
    _ = C * (((Real.sqrt t / (t * t)) * (Real.log t) ^ 10)) := by ring
    _ = C * ((1 / (t * Real.sqrt t)) * (Real.log t) ^ 10) := by rw [sqrt_div_mul_self ht]
    _ = C * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by rw [one_div]; ring

/-- Pointwise domination of `(θ t − t) / t²` on `(a, ∞)` under the bound
`|θ t − t| ≤ C √t (log t)¹⁰`, valid for `a ≥ a₀ ≥ 2`. -/
theorem theta_sub_id_integrableOn_Ioi {a₀ : ℝ} (ha0 : 2 ≤ a₀) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, a₀ ≤ t → |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t) ^ 10) :
    ∀ a : ℝ, a₀ ≤ a →
      MeasureTheory.IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / (t * t))
        (Set.Ioi a) MeasureTheory.volume := by
  intro a haa
  have _hC : 0 ≤ C := hC
  have ha2 : 2 ≤ a := le_trans ha0 haa
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ha2
  have hG0 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.log t) ^ 10 / (t * Real.sqrt t)) (Set.Ioi a) MeasureTheory.volume :=
    Commons.Analysis.Real.integrableOn_log10_div_sqrt ha2
  have hG : MeasureTheory.IntegrableOn
      (fun t : ℝ => C * ((Real.log t) ^ 10 / (t * Real.sqrt t)))
      (Set.Ioi a) MeasureTheory.volume := by
    exact hG0.const_mul C
  have hFmeas : Measurable (fun t : ℝ => (Chebyshev.theta t - t) / (t * t)) := by
    have hth : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
    exact (hth.sub measurable_id).div (measurable_id.mul measurable_id)
  have hFae : AEStronglyMeasurable (fun t : ℝ => (Chebyshev.theta t - t) / (t * t))
      (MeasureTheory.volume.restrict (Set.Ioi a)) := hFmeas.aestronglyMeasurable
  have hpt : ∀ t : ℝ, t ∈ Set.Ioi a →
      ‖(Chebyshev.theta t - t) / (t * t)‖ ≤
        C * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    intro t ht
    have hat : a < t := ht
    have ha0t : a₀ ≤ t := le_trans haa (le_of_lt hat)
    have htpos : 0 < t := lt_trans hapos hat
    calc
      ‖(Chebyshev.theta t - t) / (t * t)‖ = |Chebyshev.theta t - t| / (t * t) := by
        rw [Real.norm_eq_abs, abs_div]
        congr 1
        exact abs_of_nonneg (mul_self_nonneg t)
      _ ≤ C * Real.sqrt t * (Real.log t) ^ 10 / (t * t) :=
        div_le_div_of_nonneg_right (hb t ha0t) (mul_self_nonneg t)
      _ = C * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := theta_bound_algebra htpos
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)),
      ‖(Chebyshev.theta t - t) / (t * t)‖ ≤
        C * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht
  exact Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi a))
    (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * t))
    (g := fun t : ℝ => C * ((Real.log t) ^ 10 / (t * Real.sqrt t)))
    hG hFae hae

end Commons.NumberTheory.Zeta