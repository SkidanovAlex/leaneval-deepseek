import Mathlib
import Submission.Work.EKLC6Core.towerDefs

namespace Work.EKLC6Core

section PartitionHelpers

open MeasureTheory Set
open Work.EKLContract

/-- Each first-return set is measurable (finite union/intersection of preimages of `Ω`). -/
private theorem measurable_firstReturnSet {t : Fin 3 → ℝ} {Ω : Set X3}
    (hΩ : MeasurableSet Ω) (i : ℕ) : MeasurableSet (firstReturnSet t Ω i) := by
  have hc : Continuous (fun y : X3 => aDiag t • y) := by fun_prop
  unfold firstReturnSet
  refine ((hΩ.inter ?_).inter ?_)
  · exact (hc.measurable.iterate i) hΩ
  · exact Finset.measurableSet_biInter _ (fun j _ => (hc.measurable.iterate j hΩ).compl)

/-- The never-returning set is measurable (countable intersection of preimages of `Ω`). -/
private theorem measurable_neverReturnSet {t : Fin 3 → ℝ} {Ω : Set X3}
    (hΩ : MeasurableSet Ω) : MeasurableSet (neverReturnSet t Ω) := by
  have hc : Continuous (fun y : X3 => aDiag t • y) := by fun_prop
  unfold neverReturnSet
  exact hΩ.inter (MeasurableSet.biInter
    (Set.countable_univ.mono (Set.subset_univ _))
    (fun j _ => (hc.measurable.iterate j hΩ).compl))

/-- Unfolding of the first-return set at a positive level: the index set `Icc 1 (i - 1)`
of the definition is `{j | 1 ≤ j ∧ j < i}`. -/
private theorem firstReturnSet_eq {t : Fin 3 → ℝ} {Ω : Set X3} {i : ℕ} (hi : 1 ≤ i) :
    firstReturnSet t Ω i =
      {x : X3 | x ∈ Ω ∧ ((fun y : X3 => aDiag t • y)^[i]) x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j → j < i → ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω} := by
  ext x
  simp only [firstReturnSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hxΩ, hxi⟩, hprev⟩
    exact ⟨hxΩ, hxi, fun j hj hji => hprev j ⟨hj, by omega⟩⟩
  · rintro ⟨hxΩ, hxi, hprev⟩
    exact ⟨⟨hxΩ, hxi⟩, fun j ⟨hj1, hji⟩ => hprev j hj1 (by omega)⟩

/-- Unfolding of the never-returning set. -/
private theorem neverReturnSet_eq {t : Fin 3 → ℝ} {Ω : Set X3} :
    neverReturnSet t Ω =
      {x : X3 | x ∈ Ω ∧ ∀ j : ℕ, 1 ≤ j →
        ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω} := by
  ext x
  simp only [neverReturnSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_ofPred_eq]

/-- Distinct first-return sets are disjoint: a point cannot first return at two times. -/
private theorem disjoint_firstReturnSet {t : Fin 3 → ℝ} {Ω : Set X3} {i i' : ℕ}
    (hi : 1 ≤ i) (hi' : 1 ≤ i') (hne : i ≠ i') :
    Disjoint (firstReturnSet t Ω i) (firstReturnSet t Ω i') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [firstReturnSet_eq hi] at hx
  rw [firstReturnSet_eq hi'] at hx'
  rcases hx with ⟨-, hxi, hprev⟩
  rcases hx' with ⟨-, hxi', hprev'⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact hprev' i hi h hxi
  · exact hprev i' hi' h hxi'

/-- `Ω` is the union of the first-return sets over the positive levels and the
never-returning set. -/
private theorem union_firstReturnSet {t : Fin 3 → ℝ} {Ω : Set X3} :
    Ω = (⋃ i ∈ {i : ℕ | 1 ≤ i}, firstReturnSet t Ω i) ∪ neverReturnSet t Ω := by
  classical
  ext x
  constructor
  · intro hx
    by_cases h : ∃ i, 1 ≤ i ∧ ((fun y : X3 => aDiag t • y)^[i]) x ∈ Ω
    · left
      rw [Set.mem_iUnion₂]
      refine ⟨Nat.find h, (Nat.find_spec h).1, ?_⟩
      rw [firstReturnSet_eq (Nat.find_spec h).1]
      exact ⟨hx, (Nat.find_spec h).2,
        fun j hj hji hxj => Nat.find_min h hji ⟨hj, hxj⟩⟩
    · right
      rw [neverReturnSet_eq]
      exact ⟨hx, fun j hj hxj => h ⟨j, hj, hxj⟩⟩
  · rintro (hx | hx)
    · rw [Set.mem_iUnion₂] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      rw [firstReturnSet_eq hi] at hxi
      exact hxi.1
    · rw [neverReturnSet_eq] at hx
      exact hx.1

end PartitionHelpers

theorem firstReturn_partition {t : Fin 3 → ℝ} {Ω : Set Work.EKLContract.X3}
    (hΩ : MeasurableSet Ω) :
    (∀ i : ℕ, MeasurableSet (Work.EKLC6Core.firstReturnSet t Ω i)) ∧
    MeasurableSet (Work.EKLC6Core.neverReturnSet t Ω) ∧
    (∀ i i' : ℕ, 1 ≤ i → 1 ≤ i' → i ≠ i' →
      Disjoint (Work.EKLC6Core.firstReturnSet t Ω i) (Work.EKLC6Core.firstReturnSet t Ω i')) ∧
    Ω = (⋃ i ∈ {i : ℕ | 1 ≤ i}, Work.EKLC6Core.firstReturnSet t Ω i) ∪
      Work.EKLC6Core.neverReturnSet t Ω ∧
    (∀ i : ℕ, 1 ≤ i → Work.EKLC6Core.firstReturnSet t Ω i =
      {x : Work.EKLContract.X3 | x ∈ Ω ∧
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[i]) x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j → j < i →
          ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x ∉ Ω}) ∧
    Work.EKLC6Core.neverReturnSet t Ω =
      {x : Work.EKLContract.X3 | x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j →
          ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x ∉ Ω} := by
  refine ⟨fun i => measurable_firstReturnSet hΩ i, measurable_neverReturnSet hΩ,
    fun i i' hi hi' hne => disjoint_firstReturnSet hi hi' hne, union_firstReturnSet,
    fun i hi => firstReturnSet_eq hi, neverReturnSet_eq⟩

end Work.EKLC6Core
