import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.setIntegral_indicator_comp_eq_toReal

/-!
# `Work.EKLProd.post_null_transfer_gen`

**Converse of `Work.EKLProd.leafwise_null_transfer_gen` for an arbitrary plaque algebra.**

Let `μ` be a probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, `U ≤ SL₃(ℝ)` a subgroup with an
`IsLeafwise` system of leafwise measures `ν`, `Z ⊆ X₃` carrying a plaque algebra `m` for `U`
(Pisa Def. 6.2 / Thm 6.3(iv)), and `N` a Borel set.  If for `(μ.restrict Z)`-a.e. `x` the
`ν x`-mass of the part of the shape `shape m U x` that is mapped into `N` by `u ↦ u • x`
vanishes, then `N` is `(μ.restrict Z)`-null.

The proof reads the `condexp` field of `IsLeafwise` at the test function `f = 1_N`: for
`(μ.restrict Z)`-a.e. `x`,

`condExp m (μ.restrict Z) 1_N x = (∫_{shape m U x} 1_N (u • x) ∂ν x) / (ν x (shape m U x)).toReal`,

and the fibre hypothesis makes the numerator vanish (`setIntegral_indicator_comp_eq_toReal`), so
the conditional expectation vanishes a.e.; integrating with `MeasureTheory.integral_condExp` and
`integral_indicator_const` identifies `((μ.restrict Z) N).toReal` with `0`, whence
`(μ.restrict Z) N = 0`.  No positivity or finiteness of the shape mass is needed: the division
`0 / d` is `0` in `ℝ` for every `d`.  Nor is any measurability of `Z` or of `m` beyond the
`IsPlaqueAlgebra` hypotheses required.
-/

open MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

theorem post_null_transfer_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hν : Work.EKLContract.IsLeafwise μ U ν X')
    {Z : Set Work.EKLContract.X3} {m : MeasurableSpace Work.EKLContract.X3}
    (hm : Work.EKLContract.IsPlaqueAlgebra U Z m)
    {N : Set Work.EKLContract.X3}
    (hN : @MeasurableSet Work.EKLContract.X3 (borel Work.EKLContract.X3) N)
    (hfibre : ∀ᵐ x ∂(μ.restrict Z),
      ν x {u : Work.EKLContract.SL3 | u ∈ Work.EKLContract.shape m U x ∧ u • x ∈ N} = 0) :
    (μ.restrict Z) N = 0 := by
  -- keep `borel X3` in charge of instance search: `m` is a local hypothesis of class type
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  set F : Work.EKLContract.X3 → ℝ := N.indicator (fun _ => (1 : ℝ)) with hF
  have hFmeas : Measurable F := measurable_const.indicator hN
  have hFb : ∃ C, ∀ y, |F y| ≤ C := ⟨1, fun y => by
    by_cases hy : y ∈ N
    · rw [hF, Set.indicator_of_mem hy]; norm_num
    · rw [hF, Set.indicator_of_notMem hy]; norm_num⟩
  -- the `condexp` axiom of `IsLeafwise`, read at `f = 1_N`
  have hform := hν.condexp Z m hm F hFmeas hFb
  -- the leafwise numerator vanishes a.e.
  have hnum0 : ∀ᵐ x ∂(μ.restrict Z),
      (∫ u in Work.EKLContract.shape m U x, F (u • x) ∂(ν x)) = 0 := by
    filter_upwards [hfibre] with x hx
    rw [hF, setIntegral_indicator_comp_eq_toReal (ν := ν x) (g := fun u : SL3 => u • x)
      (S := N) ((continuous_id.smul continuous_const).measurable) hN]
    have hset : Work.EKLContract.shape m U x ∩ (fun u : SL3 => u • x) ⁻¹' N
        = {u : SL3 | u ∈ Work.EKLContract.shape m U x ∧ u • x ∈ N} := rfl
    rw [hset, hx, ENNReal.toReal_zero]
  -- hence the conditional expectation vanishes a.e. (division by zero is `0` in `ℝ`)
  have hcond0 : ∀ᵐ x ∂(μ.restrict Z), condExp m (μ.restrict Z) F x = 0 := by
    filter_upwards [hform, hnum0] with x h1 h2
    rw [h1, h2, zero_div]
  have hI : (∫ x, condExp m (μ.restrict Z) F x ∂(μ.restrict Z)) = 0 := by
    rw [integral_congr_ae hcond0, integral_zero]
  have hJ : (∫ x, condExp m (μ.restrict Z) F x ∂(μ.restrict Z))
      = (∫ x, F x ∂(μ.restrict Z)) :=
    integral_condExp hm.1
  have hFint : (∫ x, F x ∂(μ.restrict Z)) = ((μ.restrict Z) N).toReal := by
    rw [hF, integral_indicator_const (1 : ℝ) hN, smul_eq_mul, mul_one, measureReal_def]
  have htoReal : ((μ.restrict Z) N).toReal = 0 := by
    rw [← hFint, ← hJ]; exact hI
  rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h | h
  · exact h
  · exact absurd h (measure_ne_top (μ.restrict Z) N)

end Work.EKLProd
