import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Measure.Real

open MeasureTheory Metric Filter Set
open scoped Topology

/-- For a continuous compactly supported `f` vanishing on `[-1,1]`, the integral of `|f|` over an
interval `[c,d]` with `0 < c ≤ d` is at most `d ^ 2` times the weighted integral
`∫_{s>0} |f s| s^{-2} ds`. -/
theorem intervalIntegral_abs_le_sq_mul_integral_inv_sq {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hzero : ∀ s : ℝ, |s| ≤ 1 → f s = 0)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    (∫ s in c..d, |f s|) ≤ d ^ 2 * ∫ s in Set.Ioi (0 : ℝ), |f s| * (s ^ 2)⁻¹ := by
  set g : ℝ → ℝ := fun s => |f s| * (s ^ 2)⁻¹ with hg
  have hgdef : ∀ s, g s = |f s| * (s ^ 2)⁻¹ := by intro s; rw [hg]
  have hgnonneg : ∀ s, 0 ≤ g s := by
    intro s; rw [hgdef s]
    exact mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (sq_nonneg s))
  have hg0 : ∀ s, |s| ≤ 1 → g s = 0 := by
    intro s hs; rw [hgdef s, hzero s hs]; simp
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with y hy
      have hy1 : |y| ≤ 1 := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
        exact le_of_lt hy
      exact (hg0 y hy1).symm
    · have hcont : ContinuousAt (fun s : ℝ => (s ^ 2)⁻¹) x :=
        ((continuousAt_id (x := x)).pow 2).inv₀ (pow_ne_zero 2 hx)
      have hG : ContinuousAt (fun s : ℝ => |f s| * (s ^ 2)⁻¹) x :=
        (hf.continuousAt.abs).mul hcont
      exact hG.congr (Filter.Eventually.of_forall (fun s => (hgdef s).symm))
  have hgcs : HasCompactSupport g := hcs.mono (fun y hy => by
    rw [Function.mem_support] at hy ⊢
    intro hfy
    exact hy (by rw [hgdef y, hfy]; simp))
  have hgint : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgcs
  have hbound : ∀ s ∈ Set.Ioc c d, |f s| ≤ d ^ 2 * g s := by
    intro s hs
    obtain ⟨hsl, hsr⟩ := Set.mem_Ioc.mp hs
    have hspos : 0 < s := lt_trans hc hsl
    have hdpos : 0 < d := lt_of_lt_of_le hspos hsr
    have hs2pos : 0 < s ^ 2 := pow_pos hspos 2
    have hsle : s ^ 2 ≤ d ^ 2 := by
      rw [sq_le_sq, abs_of_pos hspos, abs_of_pos hdpos]
      exact hsr
    have hone : 1 ≤ d ^ 2 * (s ^ 2)⁻¹ := by
      have h := (one_le_div hs2pos).mpr hsle
      rwa [div_eq_mul_inv] at h
    calc |f s| = |f s| * 1 := by ring
      _ ≤ |f s| * (d ^ 2 * (s ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      _ = d ^ 2 * g s := by rw [hgdef s]; ring
  have hIf : IntegrableOn (fun s => |f s|) (Set.Ioc c d) volume :=
    (hf.abs.integrable_of_hasCompactSupport hcs.abs).integrableOn
  have hIg : IntegrableOn (fun s => d ^ 2 * g s) (Set.Ioc c d) volume :=
    (hgint.const_mul (d ^ 2)).integrableOn
  calc
    (∫ s in c..d, |f s|) = ∫ s in Set.Ioc c d, |f s| := intervalIntegral.integral_of_le hcd
    _ ≤ ∫ s in Set.Ioc c d, d ^ 2 * g s :=
        setIntegral_mono_on hIf hIg measurableSet_Ioc hbound
    _ = d ^ 2 * ∫ s in Set.Ioc c d, g s := integral_const_mul (d ^ 2) g
    _ ≤ d ^ 2 * ∫ s in Set.Ioi (0 : ℝ), g s := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
        exact setIntegral_mono_set hgint.integrableOn
          (Filter.Eventually.of_forall hgnonneg)
          (Filter.Eventually.of_forall (fun x hx => lt_trans hc (Set.mem_Ioc.mp hx).1))

end Commons.Measure.Real