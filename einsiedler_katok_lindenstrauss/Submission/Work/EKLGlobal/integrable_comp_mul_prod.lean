import Mathlib
import Submission.Work.EKLGlobal.conv_lt_top_of_isCompact
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLComp.LeafDefs

/-!
# Integrability of `p ↦ f (p.1 * p.2)` against `νT ⊗ νU`

Let `T, U ≤ H ≤ SL₃(ℝ)` be closed subgroups with `T` normalising `U`, `H = T · U` and
`T ⊓ U = ⊥`, and let `νT, νU` be measures finite on compacta and carried respectively by `T`
and `U`.  For a compactly supported continuous `f : SL₃(ℝ) → ℝ` the function
`p ↦ f (p.1 * p.2)` is integrable for the product measure `νT ⊗ νU`.

The argument is the push-forward (convolution) one.  The multiplication map
`mul : SL₃ × SL₃ → SL₃`, `p ↦ p.1 * p.2`, pushes `νT ⊗ νU` forward to the convolution
`conv νT νU` (`Work.EKLGlobal.conv`), and `conv νT νU` is finite on compacta by
`Work.EKLGlobal.conv_lt_top_of_isCompact`.  Hence `f` itself is integrable for `conv νT νU`
(`Continuous.integrable_of_hasCompactSupport`), and the lintegral of `‖f‖` transfers back
across the push-forward by `lintegral_map`.  A compactly supported continuous function is
a.e. strongly measurable, so this finiteness of the lintegral of the norm is exactly
integrability.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLGlobal

theorem integrable_comp_mul_prod {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {νT νU : MeasureTheory.Measure Work.EKLContract.SL3}
    (hTfin : ∀ K : Set Work.EKLContract.SL3, IsCompact K → νT K < ⊤)
    (hUfin : ∀ K : Set Work.EKLContract.SL3, IsCompact K → νU K < ⊤)
    (hTcar : νT (T : Set Work.EKLContract.SL3)ᶜ = 0) (hUcar : νU (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) :
    MeasureTheory.Integrable (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => f (p.1 * p.2))
      (νT.prod νU) := by
  classical
  haveI : IsFiniteMeasureOnCompacts νT := ⟨hTfin⟩
  haveI : IsFiniteMeasureOnCompacts νU := ⟨hUfin⟩
  -- The convolution `conv νT νU = mul_∗ (νT ⊗ νU)` is finite on compacta.
  haveI : IsFiniteMeasureOnCompacts (conv νT νU) :=
    ⟨fun K hK =>
      conv_lt_top_of_isCompact hTH hUH hnorm hcop hdisj hHc hTc hUc hTfin hUfin hTcar hUcar hK⟩
  -- Hence `f` is integrable for the convolution measure.
  have hInt : Integrable (fun y : Work.EKLContract.SL3 => f y) (conv νT νU) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfin : ∫⁻ y, ‖f y‖ₑ ∂(conv νT νU) < ∞ := hInt.hasFiniteIntegral
  -- Transfer the lintegral back along the (measurable) multiplication map.
  have hmul : Measurable (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2) :=
    measurable_fst.mul measurable_snd
  have hfmeas : Measurable (fun y : Work.EKLContract.SL3 => ‖f y‖ₑ) := f.continuous.enorm.measurable
  have h1 : ∫⁻ p, ‖f (p.1 * p.2)‖ₑ ∂(νT.prod νU) = ∫⁻ y, ‖f y‖ₑ ∂(conv νT νU) := by
    rw [show conv νT νU
        = (νT.prod νU).map
            (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2) from rfl]
    exact (lintegral_map hfmeas hmul).symm
  refine ⟨(f.continuous.comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def, h1]
  exact hfin

end Work.EKLGlobal
