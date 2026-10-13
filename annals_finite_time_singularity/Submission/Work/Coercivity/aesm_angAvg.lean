import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.Coercivity

/-- The radial weight `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn (fun z : ℝ => Spaces.w z) (Set.Ioi 0) := by
  unfold Spaces.w
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-- On `z > 0` the angular average `∫ θ in Iθ, K θ * f z θ` is `z` times the radial
density `L₁₂` of the fundamental model. -/
theorem integral_K_mul_eq_mul_L12dens (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) = z * FM.L12dens Spaces.K f z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  rw [FM.L12dens_eq (K := Spaces.K) (f := f) hz0]
  exact (mul_div_cancel₀ _ hz0).symm

/-- A.e. strong measurability of the squared angular average
`z ↦ (∫ θ in Iθ, K θ * f z θ)² * w z²` on `Iz`, for `f` satisfying the analytic hypotheses
`HardyHyp` of the chapter.

Intended proof: on `z ∈ Ioi 0` one has
`∫ θ in Iθ, K θ * f z θ = z * FM.L12dens Spaces.K f z`
(`FM.L12dens_eq` with `z ≠ 0` and `MeasureTheory.integral_div`; equivalently the density is
`(∫ θ, K θ * f z θ) / z`). Since `HardyHyp.hcont` makes `FM.L12dens Spaces.K f` continuous at
every point of `Ioi 0`, the function `z ↦ z * FM.L12dens Spaces.K f z` is `ContinuousOn`
`(Ioi 0)`, hence so is `z ↦ (z * FM.L12dens Spaces.K f z)² * (w z)²` (the weight `w` is
continuous off `0`), giving `AEStronglyMeasurable` w.r.t. `volume.restrict (Ioi 0)`. Finally
transport to `volume.restrict Spaces.Iz` using
`Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0))`
(`Iz = Ici 0` and `Ioi 0` differ by the null set `{0}`). -/
theorem aesm_angAvg (f : ℝ → ℝ → ℝ) (hf : HardyHyp f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
  -- `L₁₂` is continuous on `(0,∞)`, hence `z ↦ z * L₁₂(f)(z)` is.
  have hdens : ContinuousOn (fun z => FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hf.hcont z hz).continuousWithinAt
  have hcontM : ContinuousOn (fun z : ℝ => z * FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    continuousOn_id.mul hdens
  have hg : ContinuousOn
      (fun z : ℝ => (z * FM.L12dens Spaces.K f z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hcontM.pow 2).mul (continuousOn_w.pow 2)
  have haem_g : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (z * FM.L12dens Spaces.K f z) ^ 2 * (Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hg.aestronglyMeasurable measurableSet_Ioi
  -- the two functions agree on `(0,∞)`.
  have haeq : (fun z : ℝ => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun z : ℝ => (z * FM.L12dens Spaces.K f z) ^ 2 * (Spaces.w z) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [integral_K_mul_eq_mul_L12dens f hz]
  have haem : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    haem_g.congr haeq.symm
  -- `Iz = Ici 0` and `Ioi 0` differ by the null set `{0}`.
  rw [show Spaces.Iz = Set.Ici 0 from rfl]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := 0) (μ := MeasureTheory.volume))]
  exact haem

end Work.Coercivity
