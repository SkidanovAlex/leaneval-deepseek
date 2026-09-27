import Mathlib
import Submission.Work.EKLCompLeaf.measurable_nu

/-!
# Measurability of `x ↦ κ x (B ∩ K)`, `K` compact, `B` Borel

Let `κ : τ → Measure SL₃(ℝ)` be a family of measures such that

* for every compactly supported continuous `f : SL₃(ℝ) → ℝ`, the function
  `x ↦ ∫ g, f g ∂(κ x)` is measurable (weak measurability);
* every `κ x` is finite on compact sets.

Then for every **compact** `K` and every Borel set `B`, the function `x ↦ κ x (B ∩ K)` is
measurable.

The compact case `B` closed is `Work.EKLCompLeaf.measurable_apply_isCompact` (proved in
`measurable_nu`, by approximating `K` from above with Urysohn functions over a cofinal family of
opens).  The passage to all Borel `B` is a textbook π-λ argument
(`MeasurableSpace.induction_on_inter`), with π-system the closed sets — they generate the Borel
σ-algebra of `SL₃(ℝ)` (`borel_eq_generateFrom_isClosed`) — and with predicate
`C B _ := Measurable (fun x => κ x (B ∩ K))`:

* `B = ∅` is trivial;
* `B` closed: `B ∩ K` is compact (`IsCompact.inter_left`), so this is the compact case;
* complements: `κ x (Bᶜ ∩ K) = κ x K - κ x (B ∩ K)` because `K \ (B ∩ K) = Bᶜ ∩ K`
  (`measure_sdiff`); both terms are finite since `B ∩ K ⊆ K` and `κ x K < ∞`; the difference of
  two measurable `ℝ≥0∞`-valued functions is measurable;
* countable disjoint unions: `(⋃ i, B i) ∩ K = ⋃ i, (B i ∩ K)` and `κ x` is countably additive
  (`measure_iUnion`); a countable sum of measurable `ℝ≥0∞`-valued functions is measurable
  (`Measurable.tsum`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

namespace Work.EKLCompLeaf

/-- **Measurability of `x ↦ κ x (B ∩ K)` for Borel `B` and compact `K`.**  A weakly measurable
family of measures, finite on compacts, is measurable on all Borel subsets of any fixed compact
set. -/
theorem measurable_apply_inter_isCompact {τ : Type*} [MeasurableSpace τ]
    {κ : τ → MeasureTheory.Measure Work.EKLContract.SL3}
    (hmeas : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      Measurable fun x => ∫ g, f g ∂(κ x))
    (hν : ∀ x : τ, MeasureTheory.IsFiniteMeasureOnCompacts (κ x))
    {K : Set Work.EKLContract.SL3} (hK : IsCompact K) :
    ∀ B : Set Work.EKLContract.SL3, MeasurableSet B → Measurable fun x => κ x (B ∩ K) := by
  classical
  refine MeasurableSpace.induction_on_inter (m := borel SL3)
      (s := {s : Set SL3 | IsClosed s}) borel_eq_generateFrom_isClosed isPiSystem_isClosed
      ?_ ?_ ?_ ?_
  · -- the empty set
    simp only [Set.empty_inter, measure_empty]
    exact measurable_const
  · -- closed sets: `B ∩ K` is compact
    intro t ht
    exact measurable_apply_isCompact hmeas hν (hK.inter_left ht)
  · -- complements
    intro t htm ih
    have hmeasK : Measurable (fun x => κ x K) :=
      measurable_apply_isCompact hmeas hν hK
    have hfin : ∀ x, κ x (t ∩ K) ≠ ∞ := fun x =>
      ne_top_of_le_ne_top ((hν x).lt_top_of_isCompact hK).ne
        (measure_mono Set.inter_subset_right)
    have key : (fun x => κ x (tᶜ ∩ K)) = fun x => κ x K - κ x (t ∩ K) := by
      funext x
      have h1 : K \ (t ∩ K) = tᶜ ∩ K := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [← h1]
      exact measure_sdiff Set.inter_subset_right
        ((htm.inter hK.measurableSet).nullMeasurableSet) (hfin x)
    rw [key]
    exact hmeasK.sub ih
  · -- countable disjoint unions
    intro f hfd hfm ihf
    have key : (fun x => κ x ((⋃ i, f i) ∩ K)) = fun x => ∑' i, κ x (f i ∩ K) := by
      funext x
      rw [Set.iUnion_inter]
      exact measure_iUnion
        (fun i j hij => (hfd hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hfm i).inter hK.measurableSet)
    rw [key]
    exact Measurable.tsum ihf

end Work.EKLCompLeaf
