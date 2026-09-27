import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.isOpenMap_smul
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLC7.LeafwiseHoroDefs
import Submission.Work.EKLComp.X3Background

/-!
# `Work.EKLC7.LeafwiseGeom` — the elementary geometry used by the leafwise construction

This module collects the *cheap* topological facts about `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a closed
subgroup `U ≤ SL₃(ℝ)` which the construction of leafwise measures (Pisa Thm 6.3) needs:

* `V δ` is a neighbourhood of `1`, and the random-walk balls `Xball x δ = (V δ) • x` are open
  neighbourhoods of `x` (the orbit map `g ↦ g • x` is open);
* *local freeness at a point*: if the `U`-orbit of `x` is free, then displacements of `x` by
  elements of `U` close enough to `1` are trivial;
* *positivity of neighbourhoods*: for a probability measure `μ` on the second countable `X₃`,
  almost every `x` has every open neighbourhood of positive `μ`-measure.  This is the
  ingredient that makes the base `E` of Pisa's flowers have positive measure.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## 1. The `V`-balls -/

theorem V_mem_nhds_one {δ : ℝ} (hδ : 0 < δ) : V δ ∈ 𝓝 (1 : SL3) :=
  (Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds
    (Work.EKLContract.Lemmas.V_open_one δ hδ).2

theorem one_mem_V' {δ : ℝ} (hδ : 0 < δ) : (1 : SL3) ∈ V δ :=
  (Work.EKLContract.Lemmas.V_open_one δ hδ).2

theorem isOpen_orbitImage_V (x : X3) {δ : ℝ} (hδ : 0 < δ) :
    IsOpen ((fun g : SL3 => g • x) '' V δ) :=
  Work.EKLComp.isOpenMap_smul x _ (Work.EKLContract.Lemmas.V_open_one δ hδ).1

/-- The `V δ`-ball around `x` is a neighbourhood of `x` (Pisa's ball structure; the fifth
clause of the frozen `P_X3`, proved here unconditionally for `X₃ = SL₃(ℝ)/SL₃(ℤ)`). -/
theorem orbitImage_V_mem_nhds (x : X3) {δ : ℝ} (hδ : 0 < δ) :
    (fun g : SL3 => g • x) '' V δ ∈ 𝓝 x :=
  (isOpen_orbitImage_V x hδ).mem_nhds ⟨1, one_mem_V' hδ, one_smul _ x⟩

/-- **Local freeness at a point.**  If the `U`-orbit of `x` is free, then elements of `U` that
are close enough to the identity cannot fix `x`.  This is
`Work.EKLComp.locallyFree_compacta` at the compact set `{x}`. -/
theorem freeness_local (x : X3) (hx : ∀ u ∈ (⊤ : Subgroup SL3), u • x = x → u = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : SL3, u ∈ V δ → u • x = x → u = 1 := by
  obtain ⟨δ, hδ, hloc⟩ := Work.EKLComp.locallyFree_compacta ({x} : Set X3) isCompact_singleton
  exact ⟨δ, hδ, fun u hu hux => hloc x (Set.mem_singleton x) u hu hux⟩

/-- Local freeness at a point for an arbitrary subgroup `U ≤ SL₃(ℝ)`. -/
theorem freeness_local_U (U : Subgroup SL3) (x : X3) (hx : ∀ u ∈ U, u • x = x → u = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ U, u ∈ V δ → u • x = x → u = 1 := by
  obtain ⟨δ, hδ, hloc⟩ := Work.EKLComp.locallyFree_compacta ({x} : Set X3) isCompact_singleton
  exact ⟨δ, hδ, fun u _ hu hux => hloc x (Set.mem_singleton x) u hu hux⟩

/-! ## 2. Positivity of neighbourhoods

For a probability measure on a second countable space, almost every point has only
positive-measure neighbourhoods: the union of all open `μ`-null sets is again open and
`μ`-null, being a countable union of basis elements. -/

/-- `X₃` is a standard Borel space with the topological facts of `P_X3` (from `X3Background`). -/
theorem X3_secondCountable : SecondCountableTopology X3 := (Work.EKLComp.X3Background).2.2.1

theorem ae_isOpen_pos {μ : Measure X3} [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s := by
  haveI : SecondCountableTopology X3 := X3_secondCountable
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis X3
  have hBopen : ∀ n : ℕ, IsOpen (B n) := fun n => hB.isOpen (Set.mem_range_self n)
  set S : Set X3 := ⋃ n, if μ (B n) = 0 then B n else ∅ with hS
  have hSnull : μ S = 0 := by
    rw [hS]
    refine le_antisymm ?_ bot_le
    refine le_trans (measure_iUnion_le _) ?_
    have hz : (∑' n : ℕ, μ (if μ (B n) = 0 then B n else ∅)) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro n
      by_cases h : μ (B n) = 0
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact measure_empty
    rw [hz]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hSnull] with x hx
  intro s hs hxs
  by_contra h0
  have hμs : μ s = 0 := le_antisymm (not_lt.mp h0) bot_le
  obtain ⟨t, htB, hxt, hts⟩ := hB.exists_subset_of_mem_open hxs hs
  obtain ⟨n, rfl⟩ := htB
  have hn0 : μ (B n) = 0 := measure_mono_null hts hμs
  refine hx (by rw [hS]; exact Set.mem_iUnion.mpr ⟨n, by rw [if_pos hn0]; exact hxt⟩)

/-- The same, in the `V`-ball form used by the flowers: a.e. `x` has all its
`Xball · δ` balls of positive measure. -/
theorem ae_Xball_pos {μ : Measure X3} [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, ∀ δ : ℝ, 0 < δ → 0 < μ ((fun g : SL3 => g • x) '' V δ) := by
  filter_upwards [ae_isOpen_pos (μ := μ)] with x hx
  intro δ hδ
  exact hx _ (isOpen_orbitImage_V x hδ) ⟨1, one_mem_V' hδ, one_smul _ x⟩

end Work.EKLC7

namespace Work.EKLC7

/-- `X₃` is a standard Borel space; registered as an instance because the conditional-measure
API (`ProbabilityTheory.condExpKernel`) requires it. -/
instance instStandardBorelSpaceX3 : StandardBorelSpace Work.EKLContract.X3 :=
  (Work.EKLComp.X3Background).2.2.2.2

end Work.EKLC7
