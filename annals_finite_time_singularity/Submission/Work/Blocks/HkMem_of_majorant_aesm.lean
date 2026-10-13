import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

/-
**`HkMem` from a pointwise majorant, with only a.e. strong measurability.**

`Work.Spaces.HkMem α k f` is the pair of *honesty* requirements on the iterated `H^k`-integral
of `f`: every angular slice `θ ↦ HkIntegrand α k f z θ` (`z ∈ Iz`) is integrable on `Iθ`, and
`z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

If a majorant `M` of the integrand is known to have integrable slices `M z ·` on `Iθ` and an
integrable `θ`-integral `z ↦ ∫_θ M z θ` on `Iz`, then `HkMem α k f` follows as soon as the
integrand is measurable where it matters: a.e.-strongly-measurable on each slice (for the
`Integrable.mono'` step) and its `θ`-integral a.e.-strongly-measurable on `Iz` (for the outer
step).  The two measurability hypotheses are *not* derivable from a pointwise bound alone, so
they are carried explicitly; the domination hypothesis is pointwise on the closed quadrant, and
is converted to an a.e. statement with respect to the restricted measures by
`ae_restrict_of_forall_mem`.

The only structural input about `HkIntegrand` is its nonnegativity
(`Work.Spaces.HkIntegrand_nonneg`), which turns the pointwise bound into a bound on the norms
(as required by `Integrable.mono'`) and makes the `θ`-integral nonnegative, so that its absolute
value is bounded by `∫_θ M z θ`.
-/
theorem HkMem_of_majorant_aesm (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · -- every angular slice of the integrand is integrable on `Iθ`
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ)]
      with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono' hMz houter ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      (hMslice z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

end Work.Blocks
