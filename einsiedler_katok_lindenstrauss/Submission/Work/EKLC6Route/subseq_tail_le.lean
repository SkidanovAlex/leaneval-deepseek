import Mathlib

namespace Work.EKLC6Route

open MeasureTheory Filter

/-- Continuity from above: for an antitone sequence of null-measurable sets in a probability
space, the measure of `A n \ ⋂ i, A i` tends to `0`. -/
private lemma tendsto_measure_sdiff_iInter {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {A : ℕ → Set X} (hanti : Antitone A)
    (hmeas : ∀ j, MeasureTheory.NullMeasurableSet (A j) μ) :
    Filter.Tendsto (fun n => μ (A n \ ⋂ i, A i)) Filter.atTop (nhds 0) := by
  have hB : MeasureTheory.NullMeasurableSet (⋂ i, A i) μ :=
    MeasureTheory.NullMeasurableSet.iInter hmeas
  have hDmeas : ∀ n, MeasureTheory.NullMeasurableSet (A n \ ⋂ i, A i) μ :=
    fun n => (hmeas n).diff hB
  have hDanti : Antitone (fun n => A n \ ⋂ i, A i) :=
    fun i j hij => Set.sdiff_subset_sdiff_left (hanti hij)
  have hDfin : ∃ n, μ (A n \ ⋂ i, A i) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc μ (A 0 \ ⋂ i, A i) ≤ μ (A 0) := MeasureTheory.measure_mono Set.sdiff_subset
      _ ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop hDmeas hDanti hDfin
  have hempty : (⋂ n, (A n \ ⋂ i, A i)) = ∅ := by
    rw [show (⋂ n, (A n \ ⋂ i, A i)) = (⋂ n, A n) \ (⋂ i, A i) by
      ext x
      simp only [Set.mem_sdiff, Set.mem_iInter]
      constructor
      · rintro h
        exact ⟨fun i => (h i).1, fun hQ => (h 0).2 hQ⟩
      · rintro ⟨h1, h2⟩ i
        exact ⟨h1 i, h2⟩]
    exact Set.sdiff_self
  rw [hempty, MeasureTheory.measure_empty] at hlim
  simpa only [Function.comp_def] using hlim

/-- For an antitone sequence `A` and a strictly increasing `φ`, the intersections agree. -/
private lemma iInter_comp_eq_iInter {X : Type*} {A : ℕ → Set X} (hanti : Antitone A)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : (⋂ i, A (φ i)) = ⋂ i, A i := by
  apply le_antisymm
  · intro x hx
    rw [Set.mem_iInter] at hx ⊢
    intro n
    exact hanti (hφ.id_le n) (hx n)
  · intro x hx
    rw [Set.mem_iInter] at hx ⊢
    intro i
    exact hx (φ i)

/-- Given `g → 0` with `g 0 ≤ 1`, there is a strictly increasing `φ` with `φ 0 = 0` and
`g (φ j) ≤ (1/2)^j`. -/
private lemma exists_strictMono_le_tail (g : ℕ → ENNReal) (hg0 : g 0 ≤ 1)
    (hg : Filter.Tendsto g Filter.atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧
      ∀ j, g (φ j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
  have hε := (ENNReal.tendsto_atTop_zero).mp hg
  have hex : ∀ j, ∃ N, ∀ n ≥ N, g n ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
    fun j => hε _ (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) j))
  choose N hN using hex
  let φ : ℕ → ℕ := fun j => Nat.rec 0 (fun k prev => max (prev + 1) (N (k + 1) + 1)) j
  have hφ_succ : ∀ k, φ (k + 1) = max (φ k + 1) (N (k + 1) + 1) := fun k => rfl
  have hφ_zero : φ 0 = 0 := rfl
  refine ⟨φ, ?_, hφ_zero, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    rw [hφ_succ n]
    exact lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (le_max_left _ _)
  · intro j
    cases j with
    | zero => rw [hφ_zero]; simpa using hg0
    | succ k =>
      rw [hφ_succ k]
      exact hN (k + 1) _ (le_trans (Nat.le_succ _) (le_max_right _ _))

theorem subseq_tail_le {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] {A : ℕ → Set X} (hanti : Antitone A) (hmeas : ∀ j, MeasureTheory.NullMeasurableSet (A j) μ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ j : ℕ, μ (A (φ j) \ ⋂ i, A (φ i)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
  have hg0 : μ (A 0 \ ⋂ i, A i) ≤ 1 := by
    calc μ (A 0 \ ⋂ i, A i) ≤ μ (A 0) := MeasureTheory.measure_mono Set.sdiff_subset
      _ ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  obtain ⟨φ, hφmono, hφ0, hφbound⟩ :=
    exists_strictMono_le_tail (fun n => μ (A n \ ⋂ i, A i)) hg0
      (tendsto_measure_sdiff_iInter μ hanti hmeas)
  refine ⟨φ, hφmono, hφ0, fun j => ?_⟩
  rw [iInter_comp_eq_iInter hanti hφmono]
  exact hφbound j

end Work.EKLC6Route
