import Mathlib
import Submission.Work.Whitney.CutPush.arc_chart_cover_finite

/-!
# A chart cover of an arc's parameter interval by *compact* pieces

`exists_compact_arc_chart_cover`: the parameter interval `[a,b]` of a continuous curve `δ` in a
charted space is the union of finitely many *compact* sets `K i`, each contained in an open set `U i`
whose image under `δ` lies in a single chart source.

This is the starting point of the M1 construction (`CutPush/NOTES_STATE_S59.md` §2.1): on each piece
the sheet's tangent plane can be computed in a chart, and the compactness of `K i` is what makes the
cut-off bump of `CutPush/bump_on_compact.lean` available.
-/

namespace Work.Whitney.CutPush

open scoped Manifold
open Topology

/-- **A chart cover of an arc's parameter interval by compact pieces.** -/
theorem exists_compact_arc_chart_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [LocallyCompactSpace M]
    (δ : ℝ → M) (hδ : Continuous δ) (a b : ℝ) (hab : a ≤ b) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → M) (U : ι → Set ℝ) (K : ι → Set ℝ),
      (∀ i, IsOpen (U i)) ∧ (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧
      Set.Icc a b = ⋃ i, K i ∧
      (∀ i, ∀ u ∈ U i, δ u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source) := by
  classical
  obtain ⟨t, s, hsopen, hcov, hmem⟩ := exists_finite_arc_chart_cover (n := n) δ hδ a b hab
  set s' : ↥(Set.Icc a b) → Set ℝ := fun i => if h : i ∈ t then s ⟨i, h⟩ else ∅ with hs'def
  have hs'open : ∀ i, IsOpen (s' i) := by
    intro i
    by_cases h : i ∈ t
    · rw [hs'def]
      simp only [dif_pos h]
      exact hsopen ⟨i, h⟩
    · rw [hs'def]
      simp only [dif_neg h]
      exact isOpen_empty
  have hs'eq : ∀ (i : ↥(Set.Icc a b)) (h : i ∈ t), s' i = s ⟨i, h⟩ := by
    intro i h
    rw [hs'def]
    exact dif_pos h
  have hcov' : Set.Icc a b ⊆ ⋃ i ∈ t, s' i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz)
    refine Set.mem_iUnion₂.mpr ⟨i.1, i.2, ?_⟩
    rw [hs'eq i.1 i.2]
    have hii : (⟨i.1, i.2⟩ : ↥t) = i := Subtype.ext rfl
    rw [hii]
    exact hi
  obtain ⟨K, hKcpt, hKsub, hKeq⟩ :=
    isCompact_Icc.finite_compact_cover t s' (fun i _ => hs'open i) hcov'
  refine ⟨↥t, t.finite_toSet.fintype, fun i => δ ((i.1 : ↥(Set.Icc a b)) : ℝ), fun i => s i,
    fun i => K i.1, fun i => hsopen i, fun i => hKcpt i.1, ?_, ?_, ?_⟩
  · intro i
    have h := hKsub i.1
    rw [hs'eq i.1 i.2] at h
    exact h
  · have h1 : (⋃ i : ↥t, K i.1) = ⋃ i ∈ t, K i := by
      ext z
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i.1, i.2, hi⟩
      · rintro ⟨i, hi, hzi⟩
        exact ⟨⟨i, hi⟩, hzi⟩
    rw [h1]
    exact hKeq
  · intro i u hu
    exact hmem i u hu

end Work.Whitney.CutPush
