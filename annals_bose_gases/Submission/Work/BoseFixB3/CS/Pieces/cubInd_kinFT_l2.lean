import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMassAux.plancherel_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

noncomputable section
open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `L²` mass of the `p`-convention Fourier transform of the box indicator: by Plancherel
(`HighMassAux.plancherel_L1L2`) it is `(2π)³` times the volume `ℓ³` of `acube ℓ`.

Intended proof: `plancherel_L1L2` applied to the complexified indicator `1_{Λ(ℓ)}` (which is
in `L¹ ∩ L²`), together with `Submission.BoseGases.acube_volume`. -/
theorem cubInd_kinFT_l2 (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ∫ p : E3, ‖Submission.BoseGases.kinFT
        (fun z : E3 =>
          (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) p‖ ^ 2
      = (2 * Real.pi) ^ 3 * ℓ ^ 3 := by
  -- The complexified box indicator, as a function `E3 → ℂ`.
  set u : E3 → ℂ := fun z =>
    (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ) with hu
  have hcube : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  -- `u` is the indicator of `Λ(ℓ)` of the constant `1 : ℂ`.
  have hueq : u = (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [hu]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  -- `u` is (a.e.) strongly measurable and `∫ ‖u‖²` is the indicator of `Λ(ℓ)`.
  have hmeas : AEStronglyMeasurable u volume := by
    rw [hueq]
    exact ((measurable_const : Measurable (fun _ : E3 => (1 : ℂ))).indicator hcube).aestronglyMeasurable
  have hEqi : (fun x : E3 => ‖u x‖ ^ 2)
      = fun x : E3 => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
    funext x
    rw [hu]
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hIntOn : IntegrableOn (fun _ : E3 => (1 : ℝ)) (Submission.BoseGases.acube ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ)
      aestronglyMeasurable_const 1 (by filter_upwards with z; simp)
  have hIntOnC : IntegrableOn (fun _ : E3 => (1 : ℂ)) (Submission.BoseGases.acube ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ)
      aestronglyMeasurable_const 1 (by filter_upwards with z; simp)
  -- `u ∈ L¹` and `u ∈ L²`.
  have hint : Integrable u := by
    rw [hueq]
    exact (integrable_indicator_iff hcube).2 hIntOnC
  have hsqi : Integrable (fun x : E3 => ‖u x‖ ^ 2) := by
    rw [hEqi]
    exact (integrable_indicator_iff hcube).2 hIntOn
  have hmemLp1 : MemLp u 1 volume := memLp_one_iff_integrable.mpr hint
  have hmemLp2 : MemLp u 2 volume := (memLp_two_iff_integrable_sq_norm hmeas).2 hsqi
  -- The `L²` mass of the indicator is the volume `ℓ³` of the cube.
  have hmass : ∫ x : E3, ‖u x‖ ^ 2 = ℓ ^ 3 := by
    rw [hEqi, integral_indicator_const (1 : ℝ) hcube, Measure.real_def, smul_eq_mul,
      Submission.BoseGases.acube_volume ℓ hℓ, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
    ring
  -- Plancherel, un-normalised.
  have hpl := Work.BoseFixB3.HighMassAux.plancherel_L1L2 (u := u) hmemLp1 hmemLp2
  rw [hmass] at hpl
  have hne : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
  rw [← hpl, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end

end Work.BoseFixB3.CS.Pieces
