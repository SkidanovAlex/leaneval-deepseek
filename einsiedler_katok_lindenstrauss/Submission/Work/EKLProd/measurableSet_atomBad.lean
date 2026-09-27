import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLProd.measurable_atomShU
import Submission.Work.EKLProd.measurable_atomMargU
import Submission.Work.EKLProd.measurableSet_not_SL3Criterion
import Submission.Work.EKLC6Core.measurable_apply_section
import Submission.Work.EKLRelCross.SL3criterion
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLRelProduct.Defs

/-!
# `Work.EKLProd.measurableSet_atomBad`

The bad set `atomBad hf n XH XU νH νU` of `Work.EKLProd.AtomProductDefs` is Borel:

  `atomBad = {y | y ∈ Z n ∧ y ∈ XH ∧ y ∈ XU ∧ atomShU hf n νU y ≠ 0 ∧
                  atomMargU hf n νH y ≠ 0 ∧ ¬ SL3Criterion (atomShU …) (atomMargU …)}.`

* `Z n` is Borel (`IsPlaqueAlgebra`), and `XH`, `XU` are Borel (`IsLeafwise.meas_dom`).
* For every Borel `S ⊆ SL₃(ℝ)` the functions `y ↦ (atomShU hf n κ y) S` and
  `y ↦ (atomMargU hf n κ y) S` are measurable as soon as `κ` is a weakly measurable family of
  measures finite on compact sets (`measurable_atomShU`, `measurable_atomMargU`); this is the
  section-evaluation statement `Work.EKLC6Core.measurable_apply_section` applied to the Borel
  section sets `{(y,u) | …}`.
* `SL3Criterion` is a countable Boolean combination of the evaluations on the `π`-system
  `SL3fam`, so `{y | ¬ SL3Criterion …}` is Borel (`measurableSet_not_SL3Criterion`).

Since `IsLeafwise` only constrains `νH`, `νU` on the conull Borel sets `XH`, `XU`, the two
delegated measurability lemmas are applied to the *truncated* families
`y ↦ if y ∈ XU then νU y else 0` (and likewise for `νH`), which are weakly measurable and finite
on compacts everywhere and agree with `νU`, `νH` on `XU`, `XH`.  As `atomBad` is by construction
contained in `XH ∩ XU ∩ Z n`, this loses nothing.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The two `atomShU`-measures coincide as soon as the families agree at the base point. -/
private lemma atomShU_of_measure_eq {H T U : Subgroup SL3}
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {κ κ' : X3 → MeasureTheory.Measure SL3} {y : X3} (h : κ y = κ' y) :
    atomShU hf n κ y = atomShU hf n κ' y := by
  simp only [atomShU, Work.EKLRelProduct.uShift, h]

/-- The two `atomMargU`-measures coincide as soon as the families agree at the base point. -/
private lemma atomMargU_of_measure_eq {H T U : Subgroup SL3}
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {κ κ' : X3 → MeasureTheory.Measure SL3} {y : X3} (h : κ y = κ' y) :
    atomMargU hf n κ y = atomMargU hf n κ' y := by
  simp only [atomMargU, prodFlowerΛTP, prodFlowerΛ, h]

/-- A measure on `SL₃(ℝ)` vanishes iff it vanishes on the whole space. -/
private lemma measure_eq_zero_iff_univ (ρ : Measure SL3) :
    (ρ = 0) ↔ (ρ Set.univ = 0) :=
  ⟨fun h => by rw [h]; simp, fun h => by
    ext s _hs
    have hle : ρ s ≤ ρ Set.univ := measure_mono (Set.subset_univ s)
    rw [h] at hle
    exact le_bot_iff.mp hle⟩

theorem measurableSet_atomBad {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) :
    MeasurableSet (Work.EKLProd.atomBad hf n XH XU νH νU) := by
  classical
  -- ## Truncations of the two leafwise families, defined (and well behaved) on all of `X₃`.
  set νU' : X3 → Measure SL3 := fun y => if y ∈ XU then νU y else 0 with hνU'def
  set νH' : X3 → Measure SL3 := fun y => if y ∈ XH then νH y else 0 with hνH'def
  have hfinU : ∀ y, IsFiniteMeasureOnCompacts (νU' y) := by
    intro y
    by_cases hy : y ∈ XU
    · rw [hνU'def]; simp only [hy, if_true]; exact hνU.radon y hy
    · rw [hνU'def]; simp only [hy, if_false]; infer_instance
  have hfinH : ∀ y, IsFiniteMeasureOnCompacts (νH' y) := by
    intro y
    by_cases hy : y ∈ XH
    · rw [hνH'def]; simp only [hy, if_true]; exact hνH.radon y hy
    · rw [hνH'def]; simp only [hy, if_false]; infer_instance
  have hmeasU : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable fun y => ∫ g, f g ∂(νU' y) := by
    intro f
    have h1 : Measurable fun y => ∫ g, f g ∂(νU y) := hνU.measurable f
    have h2 : (fun y => ∫ g, f g ∂(νU' y)) =
        fun y => if y ∈ XU then ∫ g, f g ∂(νU y) else 0 := by
      funext y
      by_cases hy : y ∈ XU
      · rw [hνU'def]; simp [hy]
      · rw [hνU'def]; simp [hy]
    rw [h2]
    exact Measurable.ite hνU.meas_dom h1 measurable_const
  have hmeasH : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable fun y => ∫ g, f g ∂(νH' y) := by
    intro f
    have h1 : Measurable fun y => ∫ g, f g ∂(νH y) := hνH.measurable f
    have h2 : (fun y => ∫ g, f g ∂(νH' y)) =
        fun y => if y ∈ XH then ∫ g, f g ∂(νH y) else 0 := by
      funext y
      by_cases hy : y ∈ XH
      · rw [hνH'def]; simp [hy]
      · rw [hνH'def]; simp [hy]
    rw [h2]
    exact Measurable.ite hνH.meas_dom h1 measurable_const
  have heqU : ∀ y ∈ XU, νU' y = νU y := by
    intro y hy; rw [hνU'def]; simp [hy]
  have heqH : ∀ y ∈ XH, νH' y = νH y := by
    intro y hy; rw [hνH'def]; simp [hy]
  -- ## Measurability of the criterion and of the two non-vanishing conditions.
  have hSh : ∀ p : ℕ × Finset ℕ,
      Measurable fun y => atomShU hf n νU' y (Work.EKLRelCross.SL3fam p) :=
    fun p => measurable_atomShU hf n hmeasU hfinU hUc
      (Work.EKLRelCross.measurableSet_SL3fam p)
  have hMg : ∀ p : ℕ × Finset ℕ,
      Measurable fun y => atomMargU hf n νH' y (Work.EKLRelCross.SL3fam p) :=
    fun p => measurable_atomMargU hTH hUH hnorm hcop hdisj hHc hTc hUc hf n hmeasH hfinH
      (Work.EKLRelCross.measurableSet_SL3fam p)
  have hcrit : MeasurableSet {y : X3 |
      ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU' y) (atomMargU hf n νH' y)} :=
    measurableSet_not_SL3Criterion hSh hMg
  have hSh0 : MeasurableSet {y : X3 | atomShU hf n νU' y ≠ 0} := by
    have huniv : Measurable fun y => atomShU hf n νU' y Set.univ :=
      measurable_atomShU hf n hmeasU hfinU hUc MeasurableSet.univ
    have hh : {y : X3 | atomShU hf n νU' y ≠ 0} =
        {y : X3 | atomShU hf n νU' y Set.univ ≠ 0} :=
      Set.ext fun y => not_congr (measure_eq_zero_iff_univ (atomShU hf n νU' y))
    rw [hh]
    exact huniv (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have hMg0 : MeasurableSet {y : X3 | atomMargU hf n νH' y ≠ 0} := by
    have huniv : Measurable fun y => atomMargU hf n νH' y Set.univ :=
      measurable_atomMargU hTH hUH hnorm hcop hdisj hHc hTc hUc hf n hmeasH hfinH MeasurableSet.univ
    have hh : {y : X3 | atomMargU hf n νH' y ≠ 0} =
        {y : X3 | atomMargU hf n νH' y Set.univ ≠ 0} :=
      Set.ext fun y => not_congr (measure_eq_zero_iff_univ (atomMargU hf n νH' y))
    rw [hh]
    exact huniv (measurableSet_singleton (0 : ℝ≥0∞)).compl
  -- ## Assembly.
  have hA : MeasurableSet {y : X3 | y ∈ hf.Z n ∧ y ∈ XH ∧ y ∈ XU ∧
      atomShU hf n νU' y ≠ 0 ∧ atomMargU hf n νH' y ≠ 0 ∧
      ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU' y) (atomMargU hf n νH' y)} := by
    rw [show {y : X3 | y ∈ hf.Z n ∧ y ∈ XH ∧ y ∈ XU ∧
        atomShU hf n νU' y ≠ 0 ∧ atomMargU hf n νH' y ≠ 0 ∧
        ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU' y) (atomMargU hf n νH' y)} =
      hf.Z n ∩ XH ∩ XU ∩ {y : X3 | atomShU hf n νU' y ≠ 0} ∩
        {y : X3 | atomMargU hf n νH' y ≠ 0} ∩
        {y : X3 | ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU' y)
          (atomMargU hf n νH' y)} from by
      ext y; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto]
    have hZ : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
    exact ((((hZ.inter hνH.meas_dom).inter hνU.meas_dom).inter hSh0).inter hMg0).inter hcrit
  have hset : {y : X3 | y ∈ hf.Z n ∧ y ∈ XH ∧ y ∈ XU ∧
      atomShU hf n νU' y ≠ 0 ∧ atomMargU hf n νH' y ≠ 0 ∧
      ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU' y) (atomMargU hf n νH' y)} =
      atomBad hf n XH XU νH νU := by
    ext y
    constructor
    · rintro ⟨hz, hH, hU, h1, h2, h3⟩
      exact ⟨hz, hH, hU,
        by rw [← atomShU_of_measure_eq hf n (heqU y hU)]; exact h1,
        by rw [← atomMargU_of_measure_eq hf n (heqH y hH)]; exact h2,
        by rw [← atomShU_of_measure_eq hf n (heqU y hU),
              ← atomMargU_of_measure_eq hf n (heqH y hH)]; exact h3⟩
    · rintro ⟨hz, hH, hU, h1, h2, h3⟩
      exact ⟨hz, hH, hU,
        by rw [atomShU_of_measure_eq hf n (heqU y hU)]; exact h1,
        by rw [atomMargU_of_measure_eq hf n (heqH y hH)]; exact h2,
        by rw [atomShU_of_measure_eq hf n (heqU y hU),
              atomMargU_of_measure_eq hf n (heqH y hH)]; exact h3⟩
  rw [← hset]
  exact hA

end Work.EKLProd
