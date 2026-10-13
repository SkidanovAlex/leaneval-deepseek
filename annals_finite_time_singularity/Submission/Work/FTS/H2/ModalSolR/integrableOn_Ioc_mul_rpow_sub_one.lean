import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory

/-- For `c` with `∫_0^∞ c² < ∞` and `β ≥ 1`, the function `t ↦ c t · t ^ (β - 1)` is integrable
on `(0,z]` for every `z > 0`.  Route: `t ^ (β-1) ≤ z ^ (β-1)` on `(0,z]`, so it suffices that
`√(c t ²) ∈ L¹((0,z])`, which is Cauchy–Schwarz for `√(c t ²)` and the constant `1` on the
finite-measure set `(0,z]` (using `√(c t ²) = |c t|` and `∫_0^z c² ≤ ∫_0^∞ c²`). -/
theorem integrableOn_Ioc_mul_rpow_sub_one {c : ℝ → ℝ} {β z : ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hβ : 1 ≤ β) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (β - 1)) (Set.Ioc 0 z) := by
  have hβ' : 0 ≤ β - 1 := by linarith
  have hzβ : 0 ≤ z ^ (β - 1) := Real.rpow_nonneg hz.le _
  -- `c²` is integrable on `(0,z]`, since `(0,z] ⊆ (0,∞)`.
  have hc' : Integrable (fun t => c t ^ 2) (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
    hc.mono_set (fun _ ht => ht.1)
  -- the constant `1` is integrable on `(0,z]`, a set of finite measure.
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
    integrableOn_const (C := (1 : ℝ)) (hs := by simp)
  -- the dominating function `(z^(β-1)/2) * (c² + 1)`: AM–GM for `2|c t| ≤ (c t)² + 1`,
  -- together with the bound `t^(β-1) ≤ z^(β-1)` on `(0,z]`.
  have hdom : Integrable (fun t => (z ^ (β - 1) / 2) * (c t ^ 2 + 1))
      (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
    have h1 : Integrable (fun t => c t ^ 2 + 1) _ := hc'.add hconst
    exact h1.const_mul (z ^ (β - 1) / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have h1 : AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      hcm.mono_measure (Measure.restrict_mono (fun _ ht => ht.1) le_rfl)
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (β - 1))
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      ((Real.continuous_rpow_const hβ').measurable.aestronglyMeasurable).restrict
    exact h1.mul h2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htnn : 0 ≤ t ^ (β - 1) := Real.rpow_nonneg ht0 _
    have hle : t ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow ht0 ht.2 hβ'
    have h2 : 2 * |c t| ≤ c t ^ 2 + 1 := by
      nlinarith [sq_nonneg (|c t| - 1), abs_nonneg (c t), sq_abs (c t)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htnn]
    have key : |c t| * t ^ (β - 1) ≤ |c t| * z ^ (β - 1) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    have key2 : 2 * (|c t| * z ^ (β - 1)) ≤ z ^ (β - 1) * (c t ^ 2 + 1) := by
      have h3 := mul_le_mul_of_nonneg_left h2 hzβ
      linarith
    linarith

end Work.FTS.H2.ModalSolR
