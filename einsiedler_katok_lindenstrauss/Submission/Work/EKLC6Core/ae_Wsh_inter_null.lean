import Mathlib
import Submission.Work.EKLC6Core.AtomInfoSetup

/-!
# `EKLC6Core.ae_Wsh_inter_null`

Transfer of a `μ`-null measurable set to the leaves (Pisa §8.9, local form), stated for the
`ν x`-mass of the `U`-shape `Wsh t S U x = shape (betaAlg t S) U x` of the pull-back atom
`betaAlg t S = comap (aDiag t ·) S.m`.

The paper's input is the `condexp` field of `IsLeafwise`: for a plaque algebra `m` and a bounded
Borel `f`, the conditional expectation `E(f | m)` is the `ν x`-average of `f` over the shape of
the `m`-atom of `x`.  Applied to `f = 1_M` with `M` a `μ`-null measurable set, the left side is
`0` (`E(1_M | m) = 0` because `1_M = 0` `μ`-a.e., and `∫ E(1_M|m) = ∫ 1_M = 0`), so the average
vanishes, and since the shape has positive finite `ν x`-mass the numerator
`ν x (shape ∩ {u | u • x ∈ M})` vanishes.

Here the plaque algebra is `m = betaAlg t S`, the pull-back of `S.m` along `aDiag t ·`, which is
a plaque algebra by `isPlaqueAlgebra_betaAlg` with base set `(aDiag t ·) ⁻¹' Z` — conull because
`aDiag t ·` preserves `μ` and `μ Zᶜ = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem ae_Wsh_inter_null {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U) {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X') (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) μ μ)
    {M : Set Work.EKLContract.X3} (hM : MeasurableSet M) (hM0 : μ M = 0)
    {S : Work.EKLRelCross.MSAlg} {Z : Set Work.EKLContract.X3} (hA : Work.EKLContract.IsPlaqueAlgebra U Z S.m)
    (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ν x (Work.EKLC6Core.Wsh t S U x ∩ {u : Work.EKLContract.SL3 | u • x ∈ M}) = 0 := by
  -- the pull-back base set `(aDiag t ·) ⁻¹' Z` is conull
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hTZ
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  -- the indicator of the null set `M`
  set f : X3 → ℝ := M.indicator (fun _ : X3 => (1 : ℝ)) with hfdef
  have hf : Measurable f := measurable_const.indicator hM
  have hfnn : ∀ y, 0 ≤ f y := by
    intro y
    by_cases hy : y ∈ M
    · rw [hfdef, Set.indicator_of_mem hy]; norm_num
    · rw [hfdef, Set.indicator_of_notMem hy]
  have hfb : ∃ C, ∀ y, |f y| ≤ C := ⟨1, fun y => by
    rw [hfdef]
    by_cases hy : y ∈ M
    · rw [Set.indicator_of_mem hy, abs_one]
    · rw [Set.indicator_of_notMem hy, abs_zero]; norm_num⟩
  -- the `condexp` field of `IsLeafwise` for the pull-back plaque algebra
  have hfield := condExp_betaAlg_eq hU hL hA t hmp hZ f hf hfb
  -- `E(1_M | betaAlg) = 0` a.e.
  have hfint : ∫ x, f x ∂μ = 0 := by
    rw [hfdef, MeasureTheory.integral_indicator hM, MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, hM0]
    simp
  have hInt : ∫ x, MeasureTheory.condExp (betaAlg t S) μ f x ∂μ = 0 := by
    rw [MeasureTheory.integral_condExp (isPlaqueAlgebra_betaAlg hU hA t).1, hfint]
  have hzero : MeasureTheory.condExp (betaAlg t S) μ f =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (MeasureTheory.condExp_nonneg (Filter.Eventually.of_forall hfnn))
      MeasureTheory.integrable_condExp).mp hInt
  filter_upwards [hfield, hzero, hTZae, hX'] with x hfx hzx hxTZ hxX
  -- the shape has positive finite mass at such a point
  have hW := mass_Wsh hU hL hA t hxX hxTZ
  have hden : (ν x (Wsh t S U x)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hW.1, ne_of_lt hW.2⟩
  have hratio : (∫ u in Wsh t S U x, f (u • x) ∂(ν x)) / (ν x (Wsh t S U x)).toReal = 0 := by
    rw [← hfx, hzx]; simp
  have hnum : (∫ u in Wsh t S U x, f (u • x) ∂(ν x)) = 0 := by
    rcases div_eq_zero_iff.mp hratio with h | h
    · exact h
    · exact absurd h hden
  -- identify the integral of the indicator along the shape with the mass of the trace
  have hset : MeasurableSet {u : SL3 | u • x ∈ M} :=
    hM.preimage (continuous_id.smul continuous_const).measurable
  have hident : (∫ u in Wsh t S U x, f (u • x) ∂(ν x))
      = (ν x (Wsh t S U x ∩ {u : SL3 | u • x ∈ M})).toReal := by
    have hfun : ∀ u : SL3, f (u • x)
        = ({u : SL3 | u • x ∈ M}).indicator (fun _ : SL3 => (1 : ℝ)) u := by
      intro u
      by_cases hu : u • x ∈ M
      · rw [hfdef, Set.indicator_of_mem hu,
          Set.indicator_of_mem (show u ∈ {u : SL3 | u • x ∈ M} from hu)]
      · rw [hfdef, Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show u ∉ {u : SL3 | u • x ∈ M} from hu)]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun)]
    rw [MeasureTheory.setIntegral_indicator hset, MeasureTheory.setIntegral_const, smul_eq_mul,
      mul_one, MeasureTheory.measureReal_def, Set.inter_comm]
  rw [hident] at hnum
  have htop : ν x (Wsh t S U x ∩ {u : SL3 | u • x ∈ M}) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hW.2
  rcases (ENNReal.toReal_eq_zero_iff _).mp hnum with h | h
  · exact h
  · exact absurd h (ne_of_lt htop)

end Work.EKLC6Core
