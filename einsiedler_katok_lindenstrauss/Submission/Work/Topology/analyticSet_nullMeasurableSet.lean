import Mathlib
import Submission.Work.Topology.analyticSet_isCompact_inner

/-!
# Analytic sets are universally measurable

An analytic (Souslin) subset of a Polish space is measurable for the completion of every
finite Borel measure: it is *universally measurable*.  This is the classical theorem of
Luzin–Souslin; here it is deduced from the Choquet capacitability statement proved in
`Work.Topology.analyticSet_isCompact_inner`, namely that an analytic set `S` can be
approximated from inside in measure by compact subsets up to `ε`, relative to any minimal
measurable hull `B` of `S`.

Concretely, let `B := toMeasurable μ S` be the canonical measurable superset of `S` with
`μ B = μ S` (the outer measure of `S`).  It is minimal among measurable supersets of `S`,
so `Work.Topology.analyticSet_isCompact_inner` applies: for every `ε > 0` there is a compact
`K ⊆ S` with `μ B ≤ μ K + ε`.  Writing `μ (B \ S) ≤ μ (B \ K) = μ B - μ K ≤ ε` and letting
`ε ↓ 0` shows that `B \ S` is null, hence `S = B ∩ (B \ S)ᶜ` is null measurable.
-/

namespace Work.Topology

open MeasureTheory Set
open scoped ENNReal

/-- The only nonnegative extended real dominated by every positive extended real is `0`. -/
private lemma eq_zero_of_forall_pos_le {a : ℝ≥0∞} (h : ∀ ε : ℝ≥0∞, 0 < ε → a ≤ ε) : a = 0 := by
  by_contra hne
  have h0 : 0 < a := pos_iff_ne_zero.mpr hne
  rcases eq_or_ne a ⊤ with haT | haT
  · have h1 := h 1 one_pos
    rw [haT] at h1
    exact absurd h1 (by simp)
  · have hlt : a / 2 < a := ENNReal.half_lt_self hne haT
    exact absurd (h (a / 2) (ENNReal.half_pos hne)) (not_le.mpr hlt)

theorem analyticSet_nullMeasurableSet {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [T2Space α] [MeasurableSpace α] [BorelSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure μ] {S : Set α} (hS : MeasureTheory.AnalyticSet S) :
    MeasureTheory.NullMeasurableSet S μ := by
  classical
  -- The outer measure of `S` is realised by a measurable superset `B := toMeasurable μ S`,
  -- which is minimal among measurable supersets of `S`.
  let B : Set α := toMeasurable μ S
  have hBmeas : MeasurableSet B := measurableSet_toMeasurable μ S
  have hSB : S ⊆ B := subset_toMeasurable μ S
  have hmin : ∀ B' : Set α, MeasurableSet B' → S ⊆ B' → μ B ≤ μ B' := by
    intro B' _ hsub
    change μ (toMeasurable μ S) ≤ μ B'
    rw [measure_toMeasurable]
    exact measure_mono hsub
  have hBfin : μ B ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (subset_univ B))
  -- `B \ S` is null, by inner approximation of `S` by compacts up to `ε`.
  have hzero : μ (B \ S) = 0 := by
    refine eq_zero_of_forall_pos_le fun ε hε => ?_
    obtain ⟨K, hKc, hKS, hle⟩ := analyticSet_isCompact_inner μ hBmeas hSB hS hmin hε
    have hKB : K ⊆ B := hKS.trans hSB
    have hKfin : μ K ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hKB)
    calc μ (B \ S) ≤ μ (B \ K) :=
          measure_mono fun x hx => ⟨hx.1, fun hxK => hx.2 (hKS hxK)⟩
      _ = μ B - μ K := measure_sdiff hKB hKc.measurableSet.nullMeasurableSet hKfin
      _ ≤ ε := tsub_le_iff_right.mpr (by rw [add_comm]; exact hle)
  -- `S = B ∩ (B \ S)ᶜ` is therefore null measurable.
  have hSe : S = B ∩ (B \ S)ᶜ := by
    ext x
    constructor
    · intro hx
      exact ⟨hSB hx, fun hx' => hx'.2 hx⟩
    · rintro ⟨hxB, hx⟩
      by_contra hxS
      exact hx ⟨hxB, hxS⟩
  rw [hSe]
  exact hBmeas.nullMeasurableSet.inter (NullMeasurableSet.of_null hzero).compl

end Work.Topology
