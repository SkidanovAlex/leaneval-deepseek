import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

/-!
# A countable π-system of `SL₃(ℝ)` cut down by a compact exhaustion

This module provides the counting gadget that turns *proportionality* of two locally finite
measures on `SL₃(ℝ)` into a countable condition, hence into a measurable one.

* `SL3basisEnum` enumerates a countable topological basis of `SL₃(ℝ)` (junk value `univ`);
* `SL3fam p = compactCovering SL3 p.1 ∩ ⋂ i ∈ p.2, SL3basisEnum i`, i.e. finite intersections of
  basis elements cut down by the increasing compact exhaustion `compactCovering`;
* `SL3Criterion m1 m2` is the countable criterion for `m2 = c • m1` with `0 < c < ⊤`, the constant
  being read off the reference set `SL3fam p₀`.

The family is a π-system generating the Borel σ-algebra and contains the compact exhaustion
`n ↦ SL3fam (n, ∅) = compactCovering SL3 n`; every member is contained in a compact set, hence has
finite measure for any measure finite on compacts.
-/

open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- An enumeration of a countable topological basis of `SL₃(ℝ)` (with `univ` as the junk value). -/
noncomputable def SL3basisEnum : ℕ → Set SL3 := by
  classical
  exact fun n => if h : ∃ b : TopologicalSpace.countableBasis SL3, Encodable.encode b = n
    then ((h.choose : TopologicalSpace.countableBasis SL3) : Set _) else Set.univ

lemma SL3basisEnum_cases (n : ℕ) :
    SL3basisEnum n ∈ TopologicalSpace.countableBasis SL3 ∨ SL3basisEnum n = Set.univ := by
  classical
  by_cases h : ∃ b : TopologicalSpace.countableBasis SL3, Encodable.encode b = n
  · left
    simpa only [SL3basisEnum, dif_pos h] using h.choose.2
  · right
    simp only [SL3basisEnum, dif_neg h]

lemma SL3basisEnum_mem_range {b : Set SL3} (hb : b ∈ TopologicalSpace.countableBasis SL3) :
    ∃ n, SL3basisEnum n = b := by
  classical
  refine ⟨Encodable.encode (⟨b, hb⟩ : TopologicalSpace.countableBasis SL3), ?_⟩
  have h : ∃ c : TopologicalSpace.countableBasis SL3,
      Encodable.encode c = Encodable.encode (⟨b, hb⟩ : TopologicalSpace.countableBasis SL3) :=
    ⟨⟨b, hb⟩, rfl⟩
  have hch : ((h.choose : TopologicalSpace.countableBasis SL3) : Set _) = b := by
    rw [Encodable.encode_injective h.choose_spec]
  simpa only [SL3basisEnum, dif_pos h] using hch

/-- `SL3fam p = compactCovering SL3 p.1 ∩ ⋂ i ∈ p.2, SL3basisEnum i`. -/
def SL3fam (p : ℕ × Finset ℕ) : Set SL3 :=
  compactCovering SL3 p.1 ∩ ⋂ i ∈ p.2, SL3basisEnum i

lemma SL3fam_subset_compactCovering (p : ℕ × Finset ℕ) :
    SL3fam p ⊆ compactCovering SL3 p.1 := Set.inter_subset_left

lemma SL3fam_subset_basisEnum {p : ℕ × Finset ℕ} {i : ℕ} (hi : i ∈ p.2) :
    SL3fam p ⊆ SL3basisEnum i :=
  Set.inter_subset_right.trans (Set.biInter_subset_of_mem hi)

lemma measurableSet_SL3fam (p : ℕ × Finset ℕ) : MeasurableSet (SL3fam p) := by
  refine (isCompact_compactCovering SL3 p.1).isClosed.measurableSet.inter ?_
  refine MeasurableSet.biInter p.2.countable_toSet fun n _ => ?_
  rcases SL3basisEnum_cases n with h | h
  · exact (TopologicalSpace.isOpen_of_mem_countableBasis h).measurableSet
  · rw [h]; exact MeasurableSet.univ

lemma SL3fam_singleton_eq (k n : ℕ) : SL3fam (k, {n}) = compactCovering SL3 k ∩ SL3basisEnum n := by
  simp [SL3fam]

lemma iUnion_SL3fam_empty : (⋃ n : ℕ, SL3fam (n, ∅)) = Set.univ := by
  have hfun : (fun n : ℕ => SL3fam (n, ∅)) = fun n => compactCovering SL3 n := by
    funext n; simp [SL3fam]
  rw [hfun, iUnion_compactCovering]

lemma isPiSystem_SL3fam : IsPiSystem (Set.range SL3fam) := by
  rintro s ⟨p, rfl⟩ u ⟨q, rfl⟩ -
  refine ⟨(min p.1 q.1, p.2 ∪ q.2), ?_⟩
  ext x
  simp only [SL3fam, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
  constructor
  · rintro ⟨hmin, hrest⟩
    exact ⟨⟨compactCovering_subset SL3 (min_le_left p.1 q.1) hmin,
        fun i hi => hrest i (Or.inl hi)⟩,
      compactCovering_subset SL3 (min_le_right p.1 q.1) hmin,
      fun i hi => hrest i (Or.inr hi)⟩
  · rintro ⟨⟨hp, hp'⟩, hq, hq'⟩
    refine ⟨?_, fun i hi => hi.elim (hp' i) (hq' i)⟩
    rcases le_total p.1 q.1 with h | h
    · rw [min_eq_left h]; exact hp
    · rw [min_eq_right h]; exact hq

lemma generateFrom_SL3fam :
    MeasurableSpace.generateFrom (Set.range SL3fam) = borel SL3 := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨p, rfl⟩
    exact measurableSet_SL3fam p
  · have hborel : borel SL3 =
        MeasurableSpace.generateFrom (TopologicalSpace.countableBasis SL3) :=
      (TopologicalSpace.isBasis_countableBasis SL3).borel_eq_generateFrom
    rw [hborel]
    refine MeasurableSpace.generateFrom_le ?_
    intro b hb
    obtain ⟨n, hn⟩ := SL3basisEnum_mem_range hb
    have hb_eq : b = ⋃ k : ℕ, SL3fam (k, {n}) := by
      rw [← hn]
      refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        obtain ⟨k, hk⟩ := exists_mem_compactCovering x
        exact Set.mem_iUnion.2 ⟨k, by rw [SL3fam_singleton_eq]; exact ⟨hk, hx⟩⟩
      · intro x hx
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
        rw [SL3fam_singleton_eq] at hk
        exact hk.2
    rw [hb_eq]
    exact MeasurableSet.iUnion (f := fun k : ℕ => SL3fam (k, {n})) fun k =>
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (k, ({n} : Finset ℕ)))

/-- Countable criterion for two measures on `SL₃(ℝ)` to be proportional with a constant
`c ≠ 0, ⊤`. -/
def SL3Criterion (m1 m2 : Measure SL3) : Prop :=
  ∃ p₀ : ℕ × Finset ℕ, 0 < m1 (SL3fam p₀) ∧ 0 < m2 (SL3fam p₀) ∧
    ∀ p : ℕ × Finset ℕ, m2 (SL3fam p) * m1 (SL3fam p₀) = m1 (SL3fam p) * m2 (SL3fam p₀)

end Work.EKLRelCross
