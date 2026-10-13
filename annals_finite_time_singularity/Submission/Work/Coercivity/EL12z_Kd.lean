import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Coercivity.L12dens_sq_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.Coercivity

theorem EL12z_Kd (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi (0 : ℝ), (FM.L12dens Spaces.K f z) ^ 2
        ≤ 3 * ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 := by
  -- The angular weight integrates to `1` over `Iθ` (normalisation of `K`).
  have hK : ∫ θ in Spaces.Iθ, Spaces.K θ = (1 : ℝ) := integral_Itheta_K
  -- The reference integrand `z ↦ (∫_θ (f z θ)²)/z²` is integrable, by `HardyHyp.intB` at `j = 1`.
  have hIntR : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h := hf.intB 1 (by norm_num)
    simpa using h
  -- Pointwise (a.e.) Cauchy–Schwarz bound for the density `L12dens K f z = (1/z)∫_θ K f`.
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (FM.L12dens Spaces.K f z) ^ 2
        ≤ 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) := by
    filter_upwards [hsl, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzsl hz
    have h := L12dens_sq_slice f hK hz hzsl
    simpa only [mul_div_assoc] using h
  -- Measurability of the squared density on `(0,∞)`, from its continuity there.
  have hcontL : ContinuousOn (fun z => FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hf.hcont z hz).continuousWithinAt
  have hAesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (FM.L12dens Spaces.K f z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hcontL.aestronglyMeasurable measurableSet_Ioi).pow 2
  -- Integrability of the squared density follows by a.e. domination.
  have hdom : MeasureTheory.IntegrableOn
      (fun z => 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2)) (Set.Ioi (0 : ℝ)) :=
    hIntR.const_mul 3
  have hnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(FM.L12dens Spaces.K f z) ^ 2‖
        ≤ 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) := by
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  have hIntL : MeasureTheory.IntegrableOn
      (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hdom.mono' hAesm hnn
  refine ⟨hIntL, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntL hdom hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

end Work.Coercivity
