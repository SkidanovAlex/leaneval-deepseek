import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.OneParticleDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
The base normalisation `unitNorm = ∫ x, (unitBump x)²` is strictly positive.

`unitBump` is the `ContDiffBump unitCentre` with `rIn = 1/8 < rOut = 1/4`.

Proof.  The integrand `f x := (unitBump x)²` is nonnegative and integrable
(continuous, compactly supported).  For an integrable nonnegative `f`,
`0 < ∫ f` iff the support of `f` has positive measure
(`integral_pos_iff_support_of_nonneg`).  Here the support of the square equals
the support of the bump, i.e. `Metric.ball unitCentre (1/4)`
(`ContDiffBump.support_eq`), which has positive volume
(`Metric.measure_ball_pos`).
-/

namespace Submission

set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The normalising integral `∫ (unitBump x)²` is positive. -/
lemma unitNorm_pos : 0 < unitNorm := by
  unfold unitNorm
  have hf_nonneg : 0 ≤ (fun x : ℝ³ => (unitBump x) ^ 2) := by
    intro x
    exact sq_nonneg (unitBump x)
  have hsq_eq : (fun x : ℝ³ => (unitBump x) ^ 2) = (fun x : ℝ³ => unitBump x * unitBump x) := by
    funext x
    rw [pow_two]
  have hf_int : Integrable (fun x : ℝ³ => (unitBump x) ^ 2) := by
    rw [hsq_eq]
    have hcont : Continuous (fun x : ℝ³ => unitBump x * unitBump x) :=
      (ContDiffBump.continuous unitBumpData).mul (ContDiffBump.continuous unitBumpData)
    have hcomp : HasCompactSupport (fun x : ℝ³ => unitBump x * unitBump x) :=
      @HasCompactSupport.mul_left ℝ³ ℝ _ _ unitBump unitBump
        (ContDiffBump.hasCompactSupport unitBumpData)
    exact hcont.integrable_of_hasCompactSupport hcomp
  rw [integral_pos_iff_support_of_nonneg hf_nonneg hf_int]
  have hsupp : Function.support (fun x : ℝ³ => (unitBump x) ^ 2) =
      Metric.ball (unitCentre : ℝ³) (1 / 4) := by
    rw [hsq_eq]
    have hb : Function.support (unitBump : ℝ³ → ℝ) =
        Metric.ball (unitCentre : ℝ³) unitBumpData.rOut := by
      exact ContDiffBump.support_eq unitBumpData
    have hprod : Function.support (fun x : ℝ³ => unitBump x * unitBump x) =
        Function.support (unitBump : ℝ³ → ℝ) := by
      ext x
      simp only [Function.mem_support]
      constructor
      · intro h hx
        apply h
        rw [hx, mul_zero]
      · intro hx
        exact mul_ne_zero hx hx
    rw [hprod, hb]
    congr 1
  rw [hsupp]
  exact Metric.measure_ball_pos (volume : Measure ℝ³) (unitCentre : ℝ³)
    (by norm_num : (0 : ℝ) < 1 / 4)

end BoseGases

end Submission
