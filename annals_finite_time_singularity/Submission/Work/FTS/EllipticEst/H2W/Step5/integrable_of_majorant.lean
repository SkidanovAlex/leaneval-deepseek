import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

theorem integrable_of_majorant {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f z θ)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ ≤ M z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- `f` is squeezed between `0` and the integrable majorant `M` on the square
  -- `Iz × Iθ`, hence every `θ`-slice of `f` is integrable on `Iθ` ...
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := by
    intro z hz
    refine (hMslice z hz).mono' (hslice z hz) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
    have h1 : 0 ≤ f z θ := hnn z hz θ hθ
    have h2 : f z θ ≤ M z θ := hle z hz θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  -- ... and the `z`-function `∫ θ, f z θ` is squeezed between `0` and the
  -- integrable function `z ↦ ∫ θ, M z θ` on `Iz`.
  refine ⟨hsliceInt, ?_⟩
  refine hMz.mono' houter ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
  have hfi : MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := hsliceInt z hz
  have hMi : MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ := hMslice z hz
  have hnnI : 0 ≤ ∫ θ in Work.Spaces.Iθ, f z θ :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ hθ => hnn z hz θ hθ)
  have hmono : ∫ θ in Work.Spaces.Iθ, f z θ ≤ ∫ θ in Work.Spaces.Iθ, M z θ :=
    MeasureTheory.setIntegral_mono_on hfi hMi hIθ (fun θ hθ => hle z hz θ hθ)
  rw [Real.norm_eq_abs, abs_of_nonneg hnnI]
  exact hmono

end Work.FTS.EllipticEst.H2W.Step5
