import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

theorem hkSqSwapOpenK (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ
        = Work.Spaces.HkSq α k f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz) := by
  -- The integrand is a sum of squares, hence nonnegative.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
  -- A.e. strong measurability of the uncurried integrand, from `C^∞` on the open quadrant.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (hF.continuousOn_HkIntegrand α k)
  -- The angular slices are integrable, for every `z ∈ Iz` (hence almost every `z`).
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  -- ... and their `z`-integral is integrable.
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

end Work.FTS.StrongPersist.H6Pair6Aux
