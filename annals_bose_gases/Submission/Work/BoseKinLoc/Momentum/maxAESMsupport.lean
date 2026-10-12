import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.BoseKinLoc.Momentum

open MeasureTheory Set

/-- A measurable set `P` on which `f` agrees `μ`-a.e. with a measurable function; equivalently
`P.indicator f` is a.e. strongly measurable. -/
private def AESMGood {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (P : Set α) : Prop :=
  MeasurableSet P ∧ AEStronglyMeasurable (P.indicator f) μ

private lemma aesmGood_empty {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    AESMGood μ f ∅ := by
  refine ⟨MeasurableSet.empty, ?_⟩
  rw [Set.indicator_empty]
  exact aestronglyMeasurable_const

private lemma aesmGood_inter_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {P : Set α} (hP : AESMGood μ f P) {s : Set α} (hs : MeasurableSet s) :
    AESMGood μ f (P ∩ s) := by
  refine ⟨hP.1.inter hs, ?_⟩
  simpa [Set.indicator_indicator, Set.inter_comm] using hP.2.indicator hs

private lemma aesmGood_union {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {P Q : Set α} (hP : AESMGood μ f P) (hQ : AESMGood μ f Q) : AESMGood μ f (P ∪ Q) := by
  refine ⟨hP.1.union hQ.1, ?_⟩
  rw [aestronglyMeasurable_indicator_iff (hP.1.union hQ.1), aestronglyMeasurable_union_iff]
  exact ⟨(aestronglyMeasurable_indicator_iff hP.1).1 hP.2,
    (aestronglyMeasurable_indicator_iff hQ.1).1 hQ.2⟩

private lemma aesmGood_iUnion {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {ι : Type*} [Countable ι] {s : ι → Set α} (h : ∀ i, AESMGood μ f (s i)) :
    AESMGood μ f (⋃ i, s i) := by
  refine ⟨MeasurableSet.iUnion fun i => (h i).1, ?_⟩
  rw [aestronglyMeasurable_indicator_iff (MeasurableSet.iUnion fun i => (h i).1),
    aestronglyMeasurable_iUnion_iff]
  exact fun i => (aestronglyMeasurable_indicator_iff (h i).1).1 (h i).2

/-- For a `σ`-finite measure `μ` and any function `f : α → ℝ` there is a largest (up to null
sets) measurable set `M` on which `f` is a.e. strongly measurable, in the sense that
`M.indicator f` is a.e. strongly measurable and `N \ M` is `μ`-null for every other measurable
set `N` with this property. -/
theorem maxAESMsupport {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (hμ : MeasureTheory.SigmaFinite μ) (f : α → ℝ) :
    ∃ M : Set α, MeasurableSet M ∧ MeasureTheory.AEStronglyMeasurable (M.indicator f) μ ∧
      ∀ N : Set α, MeasurableSet N → MeasureTheory.AEStronglyMeasurable (N.indicator f) μ →
        μ (N \ M) = 0 := by
  classical
  haveI : SigmaFinite μ := hμ
  -- For each `n` (a finite-measure piece of a spanning sequence) and each `k`, a "good" set whose
  -- mass inside the `n`-th piece comes within `1/(k+1)` of the supremum of all such masses.
  have hchoice : ∀ n k : ℕ, ∃ P : Set α, AESMGood μ f P ∧
      sSup ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) '' {P | AESMGood μ f P})
        - 1 / ((k : ℝ) + 1) < (μ (P ∩ spanningSets μ n)).toReal := by
    intro n k
    have hmem : ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) ''
        {P | AESMGood μ f P}).Nonempty :=
      ⟨(μ (∅ ∩ spanningSets μ n)).toReal, ∅, aesmGood_empty μ f, rfl⟩
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup hmem
      (sub_lt_self _ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    obtain ⟨P, hP, rfl⟩ := hy
    exact ⟨P, hP, hylt⟩
  choose P hPgood hPval using hchoice
  have hbdd : ∀ n, BddAbove ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) ''
      {P | AESMGood μ f P}) := by
    intro n
    refine ⟨(μ (spanningSets μ n)).toReal, ?_⟩
    rintro x ⟨Q, -, rfl⟩
    exact ENNReal.toReal_mono (measure_spanningSets_lt_top μ n).ne
      (measure_mono Set.inter_subset_right)
  refine ⟨⋃ n, ⋃ k, (P n k ∩ spanningSets μ n), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
      (hPgood n k).1.inter (measurableSet_spanningSets μ n)
  · rw [aestronglyMeasurable_indicator_iff (MeasurableSet.iUnion fun n =>
        MeasurableSet.iUnion fun k => (hPgood n k).1.inter (measurableSet_spanningSets μ n)),
      aestronglyMeasurable_iUnion_iff]
    intro n
    rw [aestronglyMeasurable_iUnion_iff]
    intro k
    exact ((aestronglyMeasurable_indicator_iff (hPgood n k).1).1 (hPgood n k).2).mono_measure
      (Measure.restrict_mono Set.inter_subset_left le_rfl)
  · intro N hNmeas hNaesm
    have hNQ : ∀ n, AESMGood μ f (N ∩ spanningSets μ n) := by
      intro n
      exact ⟨hNmeas.inter (measurableSet_spanningSets μ n),
        by simpa [Set.indicator_indicator, Set.inter_comm] using
          hNaesm.indicator (measurableSet_spanningSets μ n)⟩
    have key : ∀ n, μ ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n))) = 0 := by
      intro n
      set Q : Set α := N ∩ spanningSets μ n with hQdef
      set Mn : Set α := ⋃ k, (P n k ∩ spanningSets μ n) with hMndef
      have hQgood : AESMGood μ f Q := by rw [hQdef]; exact hNQ n
      have hPk : ∀ k, AESMGood μ f (P n k ∩ spanningSets μ n) := fun k =>
        aesmGood_inter_measurable (hPgood n k) (measurableSet_spanningSets μ n)
      have hMngood : AESMGood μ f Mn := by rw [hMndef]; exact aesmGood_iUnion hPk
      have hfin : μ (spanningSets μ n) ≠ ⊤ := (measure_spanningSets_lt_top μ n).ne
      have hQ_sub : Q ⊆ spanningSets μ n := by rw [hQdef]; exact Set.inter_subset_right
      have hMn_sub : Mn ⊆ spanningSets μ n := by
        rw [hMndef]
        intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨k, hk⟩
        exact hk.2
      have hU_sub : Q ∪ Mn ⊆ spanningSets μ n := Set.union_subset hQ_sub hMn_sub
      have hMnn : μ Mn ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hMn_sub)
      have hUn : μ (Q ∪ Mn) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hU_sub)
      have hgoodU : AESMGood μ f (Q ∪ Mn) := aesmGood_union hQgood hMngood
      have hmemT : (μ (Q ∪ Mn)).toReal ∈
          ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) '' {P | AESMGood μ f P}) :=
        ⟨Q ∪ Mn, hgoodU, by
          show (μ ((Q ∪ Mn) ∩ spanningSets μ n)).toReal = (μ (Q ∪ Mn)).toReal
          rw [Set.inter_eq_left.mpr hU_sub]⟩
      have hbound1 : (μ (Q ∪ Mn)).toReal ≤
          sSup ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) ''
            {P | AESMGood μ f P}) := le_csSup (hbdd n) hmemT
      have hbound2 : sSup ((fun P : Set α => (μ (P ∩ spanningSets μ n)).toReal) ''
            {P | AESMGood μ f P}) ≤ (μ Mn).toReal := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        have h1 := hPval n k
        have h2 : (μ (P n k ∩ spanningSets μ n)).toReal ≤ (μ Mn).toReal :=
          ENNReal.toReal_mono hMnn
            (measure_mono (by
              rw [hMndef]
              exact Set.subset_iUnion (fun i => P n i ∩ spanningSets μ n) k))
        linarith
      have hle : μ Mn ≤ μ (Q ∪ Mn) := measure_mono Set.subset_union_right
      have hle' : μ (Q ∪ Mn) ≤ μ Mn :=
        (ENNReal.toReal_le_toReal hUn hMnn).1 (le_trans hbound1 hbound2)
      have heq : μ (Q ∪ Mn) = μ Mn := le_antisymm hle' hle
      have h0 : μ ((Q ∪ Mn) \ Mn) = 0 := by
        rw [measure_sdiff Set.subset_union_right hMngood.1.nullMeasurableSet hMnn, heq, tsub_self]
      rwa [Set.union_sdiff_right] at h0
    have hcover : N \ (⋃ n, ⋃ k, (P n k ∩ spanningSets μ n)) ⊆
        ⋃ n, ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n))) := by
      rintro x ⟨hxN, hxM⟩
      have hxs : x ∈ ⋃ n, spanningSets μ n := by
        rw [iUnion_spanningSets]; exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxs with ⟨n, hxn⟩
      refine Set.mem_iUnion.2 ⟨n, ⟨⟨hxN, hxn⟩, ?_⟩⟩
      intro hk
      exact hxM (Set.mem_iUnion.2 ⟨n, hk⟩)
    have hnull : μ (⋃ n, ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n)))) = 0 := by
      have hle : μ (⋃ n, ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n))))
          ≤ ∑' n, μ ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n))) :=
        measure_iUnion_le _
      have hzero : (∑' n, μ ((N ∩ spanningSets μ n) \ (⋃ k, (P n k ∩ spanningSets μ n)))) = 0 := by
        simp [key]
      rw [hzero] at hle
      exact le_antisymm hle (by simp)
    exact le_antisymm ((measure_mono hcover).trans_eq hnull) (by simp)

end Work.BoseKinLoc.Momentum
