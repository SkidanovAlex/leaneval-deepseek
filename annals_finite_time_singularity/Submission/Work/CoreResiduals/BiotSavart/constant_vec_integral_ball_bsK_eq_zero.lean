import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Matrix Metric

/-- **The odd-kernel cancellation.**  For a *constant* vector `v` and any centre `x` and radius `ρ`, the kernel `a ↦ ‖x-a‖⁻³ • (v ⨯ (x-a))` is odd about `a = x`: the reflection `a ↦ 2x - a` preserves `Metric.ball x ρ` and changes the sign of the integrand, so the integral vanishes. -/
theorem constant_vec_integral_ball_bsK_eq_zero (v x : Work.LWP.R3) (ρ : ℝ) :
    ∫ a in Metric.ball x ρ,
      WithLp.toLp 2 ((‖x - a‖ ^ (3 : ℕ))⁻¹ • crossProduct v (x - a)) = 0 := by
  -- Abbreviate the integrand.
  set F : Work.LWP.R3 → Work.LWP.R3 :=
    fun a => WithLp.toLp 2 ((‖x - a‖ ^ (3 : ℕ))⁻¹ • crossProduct v (x - a)) with hF
  -- The reflection `a ↦ 2 • x - a` preserves the ball `Metric.ball x ρ`.
  have hmem : ∀ a : Work.LWP.R3, (2 • x - a) ∈ Metric.ball x ρ ↔ a ∈ Metric.ball x ρ := by
    intro a
    simp only [Metric.mem_ball, dist_eq_norm]
    have h : 2 • x - a - x = x - a := by abel
    rw [h, norm_sub_rev]
  -- The integrand is odd under the reflection.
  have hodd : ∀ a : Work.LWP.R3, F (2 • x - a) = - F a := by
    intro a
    have hsubR : x - (2 • x - a) = -(x - a) := by abel
    have hsubL : x.ofLp - (2 • x - a).ofLp = -(x.ofLp - a.ofLp) := by
      rw [WithLp.ofLp_sub, WithLp.ofLp_smul]
      abel
    simp only [hF, hsubR, hsubL, norm_neg, map_neg (crossProduct v.ofLp), smul_neg,
      WithLp.toLp_neg]
  -- Hence the indicator of the ball is anti-invariant under the reflection.
  have hK : ∀ a, (Metric.ball x ρ).indicator F (2 • x - a)
      = - ((Metric.ball x ρ).indicator F a) := by
    intro a
    by_cases ha : a ∈ Metric.ball x ρ
    · have hRa : (2 • x - a) ∈ Metric.ball x ρ := (hmem a).mpr ha
      rw [Set.indicator_of_mem hRa, Set.indicator_of_mem ha, hodd a]
    · have hRa : (2 • x - a) ∉ Metric.ball x ρ := fun h => ha ((hmem a).mp h)
      rw [Set.indicator_of_notMem hRa, Set.indicator_of_notMem ha, neg_zero]
  -- The reflection is measure preserving and a measurable embedding.
  have hmp : MeasurePreserving (fun a : Work.LWP.R3 => 2 • x - a) volume volume := by
    have h := (measurePreserving_add_left volume (2 • x)).comp
      (Measure.measurePreserving_neg (volume : Measure Work.LWP.R3))
    simpa only [Function.comp_def, sub_eq_add_neg] using h
  have hRemb : MeasurableEmbedding (fun a : Work.LWP.R3 => 2 • x - a) :=
    (MeasurableEquiv.subLeft (2 • x)).measurableEmbedding
  -- The integral of the indicator therefore equals its own negative, hence vanishes.
  have hKint : ∫ a, (Metric.ball x ρ).indicator F a = 0 := by
    have hstep : ∫ a, (Metric.ball x ρ).indicator F (2 • x - a)
        = ∫ a, (Metric.ball x ρ).indicator F a :=
      hmp.integral_comp hRemb (fun a => (Metric.ball x ρ).indicator F a)
    have hpoint : (fun a => (Metric.ball x ρ).indicator F (2 • x - a))
        = fun a => - ((Metric.ball x ρ).indicator F a) := by
      funext a; exact hK a
    rw [hpoint, integral_neg] at hstep
    have h2 : (∫ a, (Metric.ball x ρ).indicator F a)
        + (∫ a, (Metric.ball x ρ).indicator F a) = 0 := (neg_eq_iff_add_eq_zero).mp hstep
    have h3 : (2 : ℝ) • (∫ a, (Metric.ball x ρ).indicator F a) = 0 := by
      rw [two_smul ℝ (∫ a, (Metric.ball x ρ).indicator F a)]; exact h2
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  rw [← integral_indicator (f := F) measurableSet_ball]
  exact hKint

end Work.CoreResiduals.BiotSavart
