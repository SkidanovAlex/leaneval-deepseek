import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

open MeasureTheory Set Filter
open scoped Real

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is `≥ 1` on `Ioo 0 (π/2)`, because there
`0 < sin(2θ) ≤ 1` and the exponent `-η` is negative. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_pos hθ
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : Real.sin (2 * θ) ^ (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_exponent_ge hsin_pos hsin_le (by rw [Work.Spaces.eta]; norm_num)
  rwa [Real.rpow_zero] at h

/-- `|x| ≤ x² + 1` for every real `x`. -/
theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  have hh : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - 1 / 2), abs_nonneg x]

/-- **The energy form dominates the plain `L²`/`L¹` norms.**

Since `thEta θ = sin(2θ)^{-η} ≥ 1` on `Ioo 0 (π/2)`, integrability of the weighted energy
`(f')²·thEta` on the open angular interval gives integrability of `(f')²` there (domination),
then of `|f'|` (via `|x| ≤ x² + 1` and finiteness of the interval), and finally of `f'` on
every subinterval `(a,b)` with `0 < a < b < π/2` (restriction of the measure).

The only regularity input is `f ∈ C¹` on the open interval, which supplies continuity — hence
a.e. strong measurability — of `deriv f` there; no differentiability at the endpoints is
needed. -/
theorem derivIntegrableOfEnergy (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo 0 (Real.pi / 2)) ∧
    (∀ a b : ℝ, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun θ => deriv f θ) (Set.Ioo a b)) := by
  have hSopen : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ContDiffOn.continuousOn_deriv_of_isOpen hf hSopen le_rfl
  have hmeas : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(f')² ≤ (f')²·thEta` pointwise, and the right-hand side is integrable
  have hsq : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hint (hmeas.pow 2) ?_
    refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo) ?_
    intro θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_thEta hθ)
  -- the constant `1` is integrable on the bounded interval
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- `|f'| ≤ (f')² + 1`
  have hsum : IntegrableOn (fun θ => (deriv f θ) ^ 2 + 1) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : Integrable (fun θ => (deriv f θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hsq
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hconst
    exact h1.add h2
  have habs : IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hsum hmeas.norm ?_
    refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo) ?_
    intro θ _
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le_sq_add_one (deriv f θ)
  refine ⟨hsq, habs, ?_⟩
  intro a b ha hb
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨lt_trans ha.1 hθ.1, lt_trans hθ.2 hb.2⟩
  have habs' : IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo a b) := habs.mono_set hsub
  have hmeas' : AEStronglyMeasurable (deriv f) (volume.restrict (Set.Ioo a b)) :=
    (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo
  refine (integrable_norm_iff hmeas').mp ?_
  show Integrable (fun θ => |deriv f θ|) (volume.restrict (Set.Ioo a b))
  exact habs'

end Work.EllipticEst.Core
