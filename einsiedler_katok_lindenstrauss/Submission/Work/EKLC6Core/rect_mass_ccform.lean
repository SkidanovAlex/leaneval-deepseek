import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.measurable_shift_integral

/-!
# `rect_mass_ccform`: the density `hP` tested against a nonnegative compactly supported
continuous function, read in `lintegral` form

`Work.EKLC6Core.rect_mass_ccform` converts the "mass identity"

    ∫ g, f g ∂νH = c * ∫ g, (∫ u, f (g * u) ∂νU) ∂νT      (`f : C_c(G, ℝ)`, `G = SL₃(ℝ)`)

into the corresponding identity for the *unnormalised* (Lebesgue) integrals

    (∫⁻ y, ofReal (f y) ∂νH).toReal
      = c * (∫⁻ g, (∫⁻ u, ofReal (f (g * u)) ∂νU) ∂νT).toReal,

for a *nonnegative* `f`.  The point is exactly that the paper's mass identity only involves
Bochner integrals of compactly supported continuous functions, while the applications below
rectangular masses are naturally stated with `∫⁻`; the two are interchangeable for nonnegative
compactly supported continuous functions (`integral_eq_lintegral_of_nonneg_ae` in one direction,
`ofReal_integral_eq_lintegral_ofReal` in the other).

Nothing about `νT` is assumed, and no finiteness of the two `∫⁻`'s is needed: the identity
`∫ a, F a ∂μ = (∫⁻ a, ofReal (F a) ∂μ).toReal` holds for *every* nonnegative (a.e. strongly)
measurable `F`, the two sides being `0` simultaneously when `F` is not integrable.  The
hypothesis `hU` is used through the fact that for each fixed `g` the function `u ↦ f (g * u)`
is continuous with compact support, so that its inner `∫⁻` is `ofReal` of its Bochner integral.
-/

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open MeasureTheory
open scoped ENNReal

/-- For a measure `ν` finite on compacts and a nonnegative continuous function `h` with compact
support, the Lebesgue integral `∫⁻ x, ofReal (h x) ∂ν` is `ofReal` of the Bochner integral.

This is `ofReal_integral_eq_lintegral_ofReal`, using that a continuous compactly supported
function is integrable for a measure which is finite on compacts. -/
theorem lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasureOnCompacts ν] {h : X → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) (hnn : ∀ x, 0 ≤ h x) :
    ∫⁻ x, ENNReal.ofReal (h x) ∂ν = ENNReal.ofReal (∫ x, h x ∂ν) := by
  have hI : Integrable h ν := hc.integrable_of_hasCompactSupport hcs
  exact (ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hnn)).symm

/-- Companion of `lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport`: the same `∫⁻` is
finite (hence `toReal` of it is the Bochner integral). -/
theorem lintegral_ofReal_lt_top_of_hasCompactSupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasureOnCompacts ν] {h : X → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) :
    ∫⁻ x, ENNReal.ofReal (h x) ∂ν < ⊤ :=
  Integrable.lintegral_lt_top (hc.integrable_of_hasCompactSupport hcs)

open MeasureTheory in
theorem rect_mass_ccform {νH νT νU : MeasureTheory.Measure Work.EKLContract.SL3}
    (hH : IsFiniteMeasureOnCompacts νH) (hU : IsFiniteMeasureOnCompacts νU)
    {c : ℝ}
    (hP : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂νH = c * ∫ g, (∫ u, f (g * u) ∂νU) ∂νT)
    (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) (hf : ∀ y, 0 ≤ f y) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂νH).toReal
      = c * (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f (g * u)) ∂νU) ∂νT).toReal := by
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts νH := hH
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts νU := hU
  -- Step 1: the left-hand side is the Bochner integral of `f` against `νH`.
  have hLHS : (∫⁻ y, ENNReal.ofReal (f y) ∂νH).toReal = ∫ y, f y ∂νH := by
    have hc : Continuous (fun y : Work.EKLContract.SL3 => f y) := by fun_prop
    rw [lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport hc f.hasCompactSupport
      (fun y => hf y), ENNReal.toReal_ofReal (integral_nonneg hf)]
  -- Step 2: for every `g`, the inner `∫⁻` is `ofReal` of the inner Bochner integral, because
  -- `u ↦ f (g * u)` is continuous with compact support (left translation is a homeomorphism).
  have hinner : ∀ g : Work.EKLContract.SL3,
      ∫⁻ u, ENNReal.ofReal (f (g * u)) ∂νU = ENNReal.ofReal (∫ u, f (g * u) ∂νU) := by
    intro g
    have hc : Continuous (fun u : Work.EKLContract.SL3 => f (g * u)) := by fun_prop
    have hcs : HasCompactSupport (fun u : Work.EKLContract.SL3 => f (g * u)) := by
      simpa [Function.comp_def, Homeomorph.coe_mulLeft] using
        (f.comp ((Homeomorph.mulLeft g).toCocompactMap)).hasCompactSupport
    exact lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport hc hcs (fun u => hf (g * u))
  -- Step 3: rewrite the outer `∫⁻` pointwise and evaluate it with
  -- `integral_eq_lintegral_of_nonneg_ae`.
  have hmeasF : Measurable (fun g : Work.EKLContract.SL3 => ∫ u, f (g * u) ∂νU) :=
    Work.EKLC6Core.measurable_shift_integral f
  have hFnn : ∀ g : Work.EKLContract.SL3, 0 ≤ ∫ u, f (g * u) ∂νU :=
    fun g => integral_nonneg (fun u => hf (g * u))
  have hJ : (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f (g * u)) ∂νU) ∂νT).toReal
      = ∫ g, (∫ u, f (g * u) ∂νU) ∂νT := by
    rw [lintegral_congr (fun g => hinner g)]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFnn)
      hmeasF.aestronglyMeasurable).symm
  -- Step 4: assemble with the hypothesis `hP`.
  rw [hLHS, hJ]
  exact hP f

end Work.EKLC6Core
