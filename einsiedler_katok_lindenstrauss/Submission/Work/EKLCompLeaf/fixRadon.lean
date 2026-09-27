import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# C8/Leaf — `fixRadon` preserves the leafwise-measure system

`Work.EKLComp.fixRadon ν X'` is the leafwise system `ν`, normalised *everywhere* by putting a
Dirac mass at the identity outside the co-null domain `X'`:

`fixRadon ν X' x = if x ∈ X' then ν x else δ_1`.

The fields of `IsLeafwise μ U ν X'` constrain `ν` only on `X'` (the sole exception being the
global measurability clause), so replacing `ν` by `fixRadon ν X'` preserves all of them, and in
addition makes `x ↦ fixRadon ν X' x` finite on compacts at *every* point of `X₃` — which is what
the global measurability arguments downstream need.

Here we prove both assertions:

* `IsLeafwise μ U (fixRadon ν X') X'`;
* `∀ x, IsFiniteMeasureOnCompacts (fixRadon ν X' x)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract

noncomputable section

namespace Work.EKLCompLeaf

/-- Outside the co-null domain `X'` the fixed system is the Dirac mass at the identity, hence
finite on compacts there; and on `X'` it is the original (finite on compacts) measure. -/
theorem isFiniteMeasureOnCompacts_fixRadon {μ : Measure X3}
    {ν : X3 → Measure SL3} {X' : Set X3} {U : Subgroup SL3}
    (hL : IsLeafwise μ U ν X') :
    ∀ x : X3, IsFiniteMeasureOnCompacts (Work.EKLComp.fixRadon ν X' x) := by
  intro x
  by_cases hx : x ∈ X'
  · rw [Work.EKLComp.fixRadon_of_mem hx]
    exact hL.radon x hx
  · rw [Work.EKLComp.fixRadon_of_notMem hx]
    exact Work.EKLComp.isFiniteMeasureOnCompacts_dirac 1

/-- `x ↦ ∫ g, f g ∂(fixRadon ν X' x)` is measurable whenever `x ↦ ∫ g, f g ∂(ν x)` is: away
from `X'` the integrand is the constant `f 1`. -/
theorem measurable_fixRadon_integral {μ : Measure X3}
    {ν : X3 → Measure SL3} {X' : Set X3} {U : Subgroup SL3}
    (hL : IsLeafwise μ U ν X') (f : CompactlySupportedContinuousMap SL3 ℝ) :
    Measurable fun x => ∫ g, f g ∂(Work.EKLComp.fixRadon ν X' x) := by
  classical
  have h : (fun x : X3 => ∫ g, f g ∂(Work.EKLComp.fixRadon ν X' x))
      = fun x : X3 =>
          if x ∈ X' then (∫ g, f g ∂(ν x)) else (∫ g, f g ∂(Measure.dirac (1 : SL3))) := by
    funext x
    by_cases hx : x ∈ X' <;> simp [Work.EKLComp.fixRadon, hx]
  rw [h]
  exact Measurable.ite hL.meas_dom (hL.measurable f) measurable_const

/-- Almost every point of `μ.restrict Z` lies in `X'`, for any `Z`. -/
theorem ae_mem_of_conull {μ : Measure X3} {X' : Set X3}
    (hmeas : MeasurableSet X') (h0 : μ X'ᶜ = 0) (Z : Set X3) :
    ∀ᵐ x ∂(μ.restrict Z), x ∈ X' := by
  have h : (μ.restrict Z) X'ᶜ = 0 := by
    rw [Measure.restrict_apply hmeas.compl]
    exact measure_mono_null Set.inter_subset_left h0
  rwa [MeasureTheory.ae_iff]

theorem fixRadon {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} {U : Subgroup Work.EKLContract.SL3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsLeafwise μ U (Work.EKLComp.fixRadon ν X') X'
      ∧ (∀ x : Work.EKLContract.X3,
          MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLComp.fixRadon ν X' x)) := by
  classical
  have hfix : ∀ x ∈ X', Work.EKLComp.fixRadon ν X' x = ν x :=
    fun x hx => Work.EKLComp.fixRadon_of_mem hx
  refine ⟨⟨hL.meas_dom, hL.conull, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx; rw [hfix x hx]; exact hL.radon x hx
  · intro x hx; rw [hfix x hx]; exact hL.carried x hx
  · intro x hx; rw [hfix x hx]; exact hL.normalised x hx
  · exact measurable_fixRadon_integral hL
  · intro x hx δ hδ; rw [hfix x hx]; exact hL.pos x hx δ hδ
  · intro x hx u hu hux; rw [hfix x hx, hfix (u • x) hux]; exact hL.equivariant x hx u hu hux
  · intro Z m hm f hf hbdd
    filter_upwards [hL.condexp Z m hm f hf hbdd,
      ae_mem_of_conull hL.meas_dom hL.conull Z] with x hx hxm
    rw [hfix x hxm]
    exact hx
  · exact isFiniteMeasureOnCompacts_fixRadon hL

end Work.EKLCompLeaf
