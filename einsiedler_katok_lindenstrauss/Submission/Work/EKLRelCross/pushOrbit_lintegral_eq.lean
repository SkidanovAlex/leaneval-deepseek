import Mathlib
import Submission.Work.EKLRelCross.LeafMeasDefs

namespace Work.EKLRelCross

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false

/-- Layer-cake form of `pushOrbit U x ν`: for a nonnegative continuous `f`, a Borel set `B` of
group elements and a measure `ν` on `X₃`, the integral of `f · 1_B` against `pushOrbit U x ν`
equals the integral over `t > 0` of `ν` of the `U`-orbit image of `{f > t} ∩ B`. -/
theorem pushOrbit_lintegral_eq {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {x : Work.EKLContract.X3}
    (hx : Function.Injective (fun u : U => ((u : Work.EKLContract.SL3) • x)))
    (ν : MeasureTheory.Measure Work.EKLContract.X3)
    {f : Work.EKLContract.SL3 → ℝ} (hf : Continuous f) (hf0 : ∀ g, 0 ≤ f g)
    {B : Set Work.EKLContract.SL3} (hB : MeasurableSet B) :
    (∫⁻ g, ENNReal.ofReal (f g) * B.indicator (fun _ => (1 : ENNReal)) g ∂(Work.EKLRelCross.pushOrbit U x ν)) = (∫⁻ t in Set.Ioi (0 : ℝ), ν (Work.EKLRelCross.orbImg U x ({g : Work.EKLContract.SL3 | t < f g} ∩ B))) := by
  haveI hSB : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  set h : Work.EKLContract.SL3 → ℝ := fun g => f g * B.indicator (fun _ => (1 : ℝ)) g with hh
  have hval : ∀ g, h g = f g * B.indicator (fun _ => (1 : ℝ)) g := by
    intro g; rw [hh]
  -- The integrand on the left is `ofReal ∘ h`.
  have hfun : ∀ g, ENNReal.ofReal (f g) * B.indicator (fun _ => (1 : ENNReal)) g
      = ENNReal.ofReal (h g) := by
    intro g
    rw [hval g]
    by_cases hg : g ∈ B
    · simp [Set.indicator_of_mem hg]
    · simp [Set.indicator_of_notMem hg]
  have hnn : 0 ≤ᵐ[Work.EKLRelCross.pushOrbit U x ν] h := by
    refine Filter.Eventually.of_forall fun g => ?_
    rw [hval g]
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, mul_one]; exact hf0 g
    · simp [Set.indicator_of_notMem hg]
  have hmble : AEMeasurable h (Work.EKLRelCross.pushOrbit U x ν) := by
    refine Measurable.aemeasurable ?_
    have : h = fun g => f g * B.indicator (fun _ => (1 : ℝ)) g := by
      funext g; exact hval g
    rw [this]
    exact hf.measurable.mul (measurable_const.indicator hB)
  have step1 : (∫⁻ g, ENNReal.ofReal (f g) * B.indicator (fun _ => (1 : ENNReal)) g
      ∂(Work.EKLRelCross.pushOrbit U x ν))
      = ∫⁻ g, ENNReal.ofReal (h g) ∂(Work.EKLRelCross.pushOrbit U x ν) :=
    lintegral_congr hfun
  rw [step1,
    lintegral_eq_lintegral_meas_lt (Work.EKLRelCross.pushOrbit U x ν) hnn hmble]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hset : {a : Work.EKLContract.SL3 | t < h a}
      = {g : Work.EKLContract.SL3 | t < f g} ∩ B := by
    have key : ∀ g, (t < h g) ↔ (t < f g ∧ g ∈ B) := by
      intro g
      rw [hval g]
      by_cases hg : g ∈ B
      · rw [Set.indicator_of_mem hg, mul_one]
        exact ⟨fun htf => ⟨htf, hg⟩, fun h => h.1⟩
      · rw [Set.indicator_of_notMem hg, mul_zero]
        exact ⟨fun hcon => absurd hcon (not_lt.mpr (le_of_lt ht0)),
          fun h => absurd h.2 hg⟩
    ext g
    exact key g
  rw [hset]
  rw [Work.EKLRelCross.pushOrbit_apply_of_injective (U := U) hUcl hx ν
    ((measurableSet_lt measurable_const hf.measurable).inter hB)]
  simp only [Work.EKLRelCross.orbImg]

end Work.EKLRelCross
