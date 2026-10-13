import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set

/-- The weight `r ↦ (1/(1+r))²` is integrable on `(0,∞)` and its integral is at most `2`
(actually `= 1`).  This is the second Cauchy–Schwarz factor in the estimate
`|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}` of Elgindi's Proposition `muestimate`: the radial singular factor
`1/r` is split as `((1+r)/r) · (1/(1+r))`, and the tail weight `(1/(1+r))²` is integrable.

Intended proof: split `(0,∞) = Ioc 0 1 ∪ Ioi 1`; on `Ioc 0 1` the integrand is `≤ 1` (finite
measure), on `Ioi 1` it is `≤ r^{-2}` whose integral is `1`
(`MeasureTheory.integral_Ioi_rpow_of_lt` with exponent `-2`; for the integrability
`MeasureTheory.integrableOn_Ioi_rpow_of_lt`).  Any bound `≤ 2` and any proof of
`IntegrableOn` on `Ioi 0` is acceptable; the exact value `1` is not needed. -/
theorem InvOneAddSq :
    MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := by
  have hmeas : Measurable fun r : ℝ => (1 / (1 + r)) ^ 2 := by fun_prop
  have hfin : volume (Ioc (0 : ℝ) 1) < ⊤ := by rw [Real.volume_Ioc]; simp
  have hsplit : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  -- pointwise bounds on the two halves of the split
  have hbdIoc : ∀ r ∈ Ioc (0 : ℝ) 1, (1 / (1 + r)) ^ 2 ≤ 1 := by
    intro r hr
    have h1 : 0 < 1 + r := by linarith [hr.1]
    have hnn : 0 ≤ 1 / (1 + r) := by positivity
    have hle : 1 / (1 + r) ≤ 1 := by rw [div_le_one h1]; linarith [hr.1]
    exact pow_le_one₀ hnn hle
  have hbdIoi : ∀ r ∈ Ioi (1 : ℝ), (1 / (1 + r)) ^ 2 ≤ r ^ (-2 : ℝ) := by
    intro r hr
    have hr0 : 0 < r := by have := mem_Ioi.mp hr; linarith
    have h1 : (r : ℝ) ≤ 1 + r := by linarith
    have h2 : (1 : ℝ) / (1 + r) ≤ 1 / r := one_div_le_one_div_of_le hr0 h1
    have h3 : (1 / (1 + r)) ^ 2 ≤ (1 / r) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (1 / r) ^ 2 = r ^ (-2 : ℝ) := by
      rw [div_pow, one_pow]
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hr0.le, Real.rpow_two,
        inv_eq_one_div]
    exact h3.trans h4.le
  -- integrability on `Ioc 0 1`: bounded by `1` on a set of finite measure
  have hIoc_int : IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound (μ := volume) hfin hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have h1 : 0 < 1 + r := by have := (mem_Ioc.mp hr).1; linarith
    rw [Real.norm_of_nonneg (pow_nonneg (by positivity) 2)]
    exact hbdIoc r hr
  -- integrability on `Ioi 1`: dominated by `r ↦ r ^ (-2)`
  have hIoi_int : IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Ioi (1 : ℝ)) := by
    have hg : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have h1 : 0 < 1 + r := by have := mem_Ioi.mp hr; linarith
    rw [Real.norm_of_nonneg (pow_nonneg (by positivity) 2)]
    exact hbdIoi r hr
  -- integrability on the whole half-line
  have hIoi0_int : IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Ioi (0 : ℝ)) := by
    rw [← hsplit]
    exact hIoc_int.union hIoi_int
  -- the two halves contribute at most `1` each
  have hIoc_le : (∫ r in Ioc (0 : ℝ) 1, (1 / (1 + r)) ^ 2) ≤ 1 := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (C := (1 : ℝ)) (by rw [Real.volume_Ioc]; simp) (by simp)
    refine (setIntegral_mono_on hIoc_int hc measurableSet_Ioc (fun r hr => hbdIoc r hr)).trans ?_
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc]
  have hIoi1_le : (∫ r in Ioi (1 : ℝ), (1 / (1 + r)) ^ 2) ≤ 1 := by
    have hg : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    refine (setIntegral_mono_on hIoi_int hg measurableSet_Ioi (fun r hr => hbdIoi r hr)).trans ?_
    rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1)]
    norm_num
  constructor
  · exact hIoi0_int
  · calc (∫ r in Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        = ∫ r in Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ), (1 / (1 + r)) ^ 2 := by rw [hsplit]
      _ = (∫ r in Ioc (0 : ℝ) 1, (1 / (1 + r)) ^ 2)
            + (∫ r in Ioi (1 : ℝ), (1 / (1 + r)) ^ 2) := by
            rw [setIntegral_union (by
              rw [Set.disjoint_left]
              rintro x ⟨_, hx1⟩ (hx2 : (1 : ℝ) < x)
              exact absurd hx2 (not_lt.mpr hx1)) measurableSet_Ioi hIoc_int hIoi_int]
      _ ≤ 1 + 1 := add_le_add hIoc_le hIoi1_le
      _ = 2 := by norm_num

end Work.FTS.H2
