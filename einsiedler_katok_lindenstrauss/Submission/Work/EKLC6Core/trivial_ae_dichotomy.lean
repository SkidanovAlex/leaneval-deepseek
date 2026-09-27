import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.TrivAeDefs
import Submission.Work.EKLC6Core.goodSet_subset_dirac
import Submission.Work.EKLC6Core.dirac_iff_aDiag_smul
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.trivial_ae_dichotomy`

For an `A`-ergodic probability `μ` and a leafwise system `ν = μ_x^U` (with the `A`-covariance on a
conull set), a.e. either `ν x = δ₁` or `ν x ≠ δ₁`.

The set `{x | ν x = δ₁}` is `A`-invariant (`dirac_iff_aDiag_smul`), so ergodicity forces it to be
null or conull.  Its measurability is not immediate from the contract (`IsLeafwise.measurable` only
gives measurability of `x ↦ ∫ f dν x` for compactly supported continuous `f`), so we replace it by
the *measurable* set `goodSet ν X'` (`TrivAeDefs`), which agrees with `{x | ν x = δ₁}` on the
conull set `X'` (`goodSet_subset_dirac`, `mem_goodSet_of_dirac`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open Work.EKLContract

theorem trivial_ae_dichotomy {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hErg : Work.EKLContract.IsAErgodic μ) :
    (∀ᵐ x ∂μ, ν x = MeasureTheory.Measure.dirac 1) ∨
      (∀ᵐ x ∂μ, ν x ≠ MeasureTheory.Measure.dirac 1) := by
  classical
  -- a measurable conull subset of `X''`
  set X₂ : Set X3 := (toMeasurable μ (X''ᶜ))ᶜ with hX₂def
  have hX₂meas : MeasurableSet X₂ := by
    rw [hX₂def]; exact (measurableSet_toMeasurable μ X''ᶜ).compl
  have hX₂conull : μ X₂ᶜ = 0 := by
    rw [hX₂def, compl_compl, measure_toMeasurable]
    exact hX''
  have hX₂sub : X₂ ⊆ X'' := by
    intro x hx
    rw [hX₂def] at hx
    simp only [Set.mem_compl_iff] at hx
    by_contra hcon
    exact hx (subset_toMeasurable μ X''ᶜ hcon)
  -- the conull measurable set `X' ∩ X₂`
  have hCmeas : MeasurableSet (X' ∩ X₂) := hL.meas_dom.inter hX₂meas
  have hCconull : μ (X' ∩ X₂)ᶜ = 0 := by
    have hsub : (X' ∩ X₂)ᶜ ⊆ X'ᶜ ∪ X₂ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and] at hx
      by_cases h : x ∈ X'
      · exact Or.inr (hx h)
      · exact Or.inl h
    refine le_antisymm ?_ zero_le
    calc μ (X' ∩ X₂)ᶜ ≤ μ (X'ᶜ ∪ X₂ᶜ) := measure_mono hsub
      _ = 0 := measure_union_null hL.conull hX₂conull
  -- the good set is measurable and `A`-invariant
  have hGmeas : MeasurableSet (goodSet ν X') := measurableSet_goodSet hL
  have hinv : ∀ t : Fin 3 → ℝ,
      (fun x : X3 => aDiag t • x) ⁻¹' (goodSet ν X') =ᵐ[μ] goodSet ν X' := by
    intro t
    have hpreconull : μ (((fun x : X3 => aDiag t • x)) ⁻¹' (X' ∩ X₂))ᶜ = 0 := by
      rw [← Set.preimage_compl]
      exact (MeasureTheory.MeasurePreserving.measure_preimage (hErg.1 t)
        hCmeas.compl.nullMeasurableSet).trans hCconull
    have hmain : ∀ᵐ x ∂μ, ((aDiag t • x) ∈ goodSet ν X') ↔ (x ∈ goodSet ν X') := by
      filter_upwards [MeasureTheory.ae_iff.mpr hCconull,
        MeasureTheory.ae_iff.mpr hpreconull] with x hxC hxpre
      have hl : x ∈ goodSet ν X' ↔ ν x = MeasureTheory.Measure.dirac 1 :=
        ⟨fun h => goodSet_subset_dirac hL h, fun h => mem_goodSet_of_dirac hxC.1 h⟩
      have hr : aDiag t • x ∈ goodSet ν X' ↔
          ν (aDiag t • x) = MeasureTheory.Measure.dirac 1 :=
        ⟨fun h => goodSet_subset_dirac hL h, fun h => mem_goodSet_of_dirac hxpre.1 h⟩
      exact hr.trans ((dirac_iff_aDiag_smul hL hcov t ⟨hxC.1, hX₂sub hxC.2⟩
        ⟨hxpre.1, hX₂sub hxpre.2⟩).symm.trans hl.symm)
    filter_upwards [hmain] with x hx
    exact propext hx
  rcases hErg.2 (goodSet ν X') hGmeas hinv with hG0 | hG1
  · -- `μ (goodSet) = 0`: the leafwise measures are nontrivial a.e.
    right
    rw [MeasureTheory.ae_iff]
    have hsub : {x : X3 | ¬ (ν x ≠ MeasureTheory.Measure.dirac 1)} ⊆
        goodSet ν X' ∪ X'ᶜ := by
      intro x hx
      simp only [Set.mem_ofPred_eq, not_not] at hx
      by_cases hxX' : x ∈ X'
      · exact Or.inl (mem_goodSet_of_dirac hxX' hx)
      · exact Or.inr hxX'
    refine le_antisymm ?_ zero_le
    calc μ {x : X3 | ¬ (ν x ≠ MeasureTheory.Measure.dirac 1)}
        ≤ μ (goodSet ν X' ∪ X'ᶜ) := measure_mono hsub
      _ ≤ μ (goodSet ν X') + μ X'ᶜ := measure_union_le _ _
      _ = 0 := by rw [hG0, hL.conull, add_zero]
  · -- `μ (goodSet)ᶜ = 0`: the leafwise measures are trivial a.e.
    left
    rw [MeasureTheory.ae_iff]
    have hsub : {x : X3 | ¬ (ν x = MeasureTheory.Measure.dirac 1)} ⊆ (goodSet ν X')ᶜ := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hx ⊢
      intro hxg
      exact hx (goodSet_subset_dirac hL hxg)
    refine le_antisymm ?_ zero_le
    calc μ {x : X3 | ¬ (ν x = MeasureTheory.Measure.dirac 1)} ≤ μ ((goodSet ν X')ᶜ) :=
          measure_mono hsub
      _ = 0 := hG1

end Work.EKLC6Core
