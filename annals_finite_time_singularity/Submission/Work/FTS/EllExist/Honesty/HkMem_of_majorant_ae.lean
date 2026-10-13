import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Blocks.HkMem_of_majorant_aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory

/-
`HkMem α k f` from a majorant `M` known to have integrable slices and an integrable
`θ`-integral, where the domination `HkIntegrand α k f ≤ M` is only required *a.e. in `θ`*
on each slice (rather than at every `θ ∈ Iθ`).

This is the a.e. form of `Work.Blocks.HkMem_of_majorant_aesm`: the same `Integrable.mono'`
argument, with the pointwise domination replaced by the a.e. one in the `θ`-integral bound
(`integral_mono_of_nonneg` accepts an a.e. hypothesis directly).  The only structural input
on `HkIntegrand` is its nonnegativity.
-/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · -- every angular slice of the integrand is integrable on `Iθ`
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [hle z hz] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono' hMz houter ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      ((hle z hz).mono fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hMslice z hz) (hle z hz)

end Work.FTS.EllExist.Honesty
