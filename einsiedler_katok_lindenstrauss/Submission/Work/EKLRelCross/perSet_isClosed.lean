import Mathlib
import Submission.Work.EKLRelCross.PeriodDefs

/-!
# Closedness of the period set `PerSet ν i j hij x`

`PerSet ν i j hij x = {τ : ℝ | (ν x).map (· * u_ij(τ)) = ν x}` is the stabiliser of the
Radon measure `ν x` inside the root group `U_ij ≅ ℝ`; here `x` is a point of `X₃` and `ν` is a
leafwise family.  The stabiliser of a Radon measure under a continuous family of continuous
transformations is closed, and this file records that fact.

The argument is the standard one: by `Measure.ext_of_integral_eq_on_compactlySupported`, a
Radon measure on `SL₃(ℝ)` is determined by its integrals against compactly supported continuous
functions, so

`PerSet ν i j hij x = ⋂_{f ∈ C_c(SL₃)} {τ | ∫ g, f (g * u_ij(τ)) ∂(ν x) = ∫ g, f g ∂(ν x)}`,

an intersection of level sets of the *continuous* functions
`τ ↦ ∫ g, f (g * u_ij(τ)) ∂(ν x)` (`Work.EKLRelCross.continuous_integral_translate_uij`,
proved in `PeriodDefs`).  Each level set is closed, hence so is the intersection.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.multiGoal false

noncomputable section

theorem perSet_isClosed (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {i j : Fin 3} (hij : i ≠ j) (x : Work.EKLContract.X3)
    (hν : MeasureTheory.IsFiniteMeasureOnCompacts (ν x)) :
    IsClosed (Work.EKLRelCross.PerSet ν i j hij x) := by
  haveI : IsFiniteMeasureOnCompacts (ν x) := hν
  haveI : IsLocallyFiniteMeasure (ν x) := inferInstance
  -- A Radon measure is determined by its integrals against compactly supported continuous
  -- functions, so `PerSet` is the intersection of the level sets `∫ f d(ν⨯u_ij(τ)) = ∫ f dν`.
  have heq : PerSet ν i j hij x = ⋂ (f : CompactlySupportedContinuousMap SL3 ℝ),
      {τ : ℝ | ∫ g, f (g * uij hij τ) ∂(ν x) = ∫ g, f g ∂(ν x)} := by
    ext τ
    simp only [PerSet, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hτ f
      have h := congrArg (fun (m : Measure SL3) => ∫ g, f g ∂m) hτ
      have h1 : ∫ g, f g ∂((ν x).map (fun g => g * uij hij τ)) =
          ∫ g, f (g * uij hij τ) ∂(ν x) :=
        integral_map (μ := ν x) (Work.EKLC7.measurable_mulRight_uij hij τ).aemeasurable
          f.continuous.aestronglyMeasurable
      exact h1.symm.trans h
    · intro h
      -- the pushforward is Radon (right translation by `u_ij(τ)` is a homeomorphism)
      haveI : ((ν x).map (fun g => g * uij hij τ)).Regular :=
        Measure.Regular.map (μ := ν x) (Homeomorph.mulRight (uij hij τ))
      refine Measure.ext_of_integral_eq_on_compactlySupported (fun f => ?_)
      have h1 : ∫ g, f g ∂((ν x).map (fun g => g * uij hij τ)) =
          ∫ g, f (g * uij hij τ) ∂(ν x) :=
        integral_map (μ := ν x) (Work.EKLC7.measurable_mulRight_uij hij τ).aemeasurable
          f.continuous.aestronglyMeasurable
      rw [h1]
      exact h f
  rw [heq]
  exact isClosed_iInter fun f =>
    IsClosed.preimage (continuous_integral_translate_uij (ν x) f hij) isClosed_singleton

end

end Work.EKLRelCross
