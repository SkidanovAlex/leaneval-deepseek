import Mathlib

namespace Work.EKLC6Core

open MeasureTheory Set

/-- From an a.e. invariant measurable set `A` under a measure preserving self-map `T`
one can find a *strictly* invariant measurable set `B` differing from `A` by a null set. -/
theorem invariant_hull {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (T : X → X) (hT : Measurable T)
    (hmp : MeasureTheory.MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A)
    (h : T ⁻¹' A =ᵐ[μ] A) :
    ∃ B : Set X, MeasurableSet B ∧ T ⁻¹' B = B ∧ μ (A \ B ∪ (B \ A)) = 0 := by
  classical
  -- the "defect": the points where membership in `A` changes under `T`.
  set D : Set X := (T ⁻¹' A \ A) ∪ (A \ T ⁻¹' A) with hDdef
  have hDmeas : MeasurableSet D := by
    rw [hDdef]; exact ((hT hA).diff hA).union (hA.diff (hT hA))
  have hDnull : μ D = 0 := by
    obtain ⟨h1, h2⟩ := (MeasureTheory.ae_eq_set).mp h
    rw [hDdef]; exact measure_union_null h1 h2
  -- the orbit of the defect is null.
  set N : Set X := ⋃ n : ℕ, (T^[n]) ⁻¹' D with hNdef
  have hNmeas : MeasurableSet N := by
    rw [hNdef]; exact MeasurableSet.iUnion fun n => (hT.iterate n) hDmeas
  have hNnull : μ N = 0 := by
    rw [hNdef]
    apply measure_iUnion_null
    intro n
    rw [(hmp.iterate n).measure_preimage hDmeas.nullMeasurableSet, hDnull]
  -- `N` is forward invariant.
  have hNinv : T ⁻¹' N ⊆ N := by
    intro x hx
    rw [mem_preimage] at hx
    rw [hNdef] at hx ⊢
    rw [mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    rw [mem_preimage] at hn
    exact ⟨n.succ, by rw [mem_preimage, Function.iterate_succ_apply]; exact hn⟩
  have hTc : ∀ x, x ∉ N → T x ∉ N :=
    fun x hxN hTx => hxN (hNinv (mem_preimage.mpr hTx))
  -- off `N`, membership in `A` is invariant under `T`.
  have hmeminv : ∀ x, x ∉ N → (x ∈ A ↔ T x ∈ A) := by
    intro x hxN
    have hxD : x ∉ D := fun hh =>
      hxN (by rw [hNdef]; exact mem_iUnion.mpr ⟨0, by rw [mem_preimage, Function.iterate_zero_apply]; exact hh⟩)
    simp only [hDdef, mem_union, mem_sdiff, not_or, not_and, not_not] at hxD
    exact ⟨fun hx => mem_preimage.mp (hxD.2 hx), fun hTx => hxD.1 (mem_preimage.mpr hTx)⟩
  have hconst : ∀ n : ℕ, ∀ x, x ∉ N → (x ∈ A ↔ (T^[n]) x ∈ A) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ k ih =>
        intro x hxN
        rw [Function.iterate_succ_apply]
        exact (hmeminv x hxN).trans (ih (T x) (hTc x hxN))
  -- the invariant hull.
  set B : Set X := ⋃ n : ℕ, (T^[n]) ⁻¹' (A \ N) with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact MeasurableSet.iUnion fun n => (hT.iterate n) (hA.diff hNmeas)
  have hmemB : ∀ x, x ∈ B ↔ ∃ n : ℕ, (T^[n]) x ∈ A \ N := by
    intro x; rw [hBdef]; simp only [mem_iUnion, mem_preimage]
  have hsub1 : T ⁻¹' B ⊆ B := by
    intro x hx
    rw [mem_preimage] at hx
    rw [hmemB (T x)] at hx
    rw [hmemB x]
    obtain ⟨n, hn⟩ := hx
    refine ⟨n.succ, ?_⟩
    rw [Function.iterate_succ_apply]
    exact hn
  have hsub2 : B ⊆ T ⁻¹' B := by
    intro x hx
    rw [mem_preimage]
    rw [hmemB x] at hx
    rw [hmemB (T x)]
    obtain ⟨n, hn⟩ := hx
    rcases n with _ | k
    · have hn' : x ∈ A \ N := by
        rw [Function.iterate_zero_apply] at hn; exact hn
      refine ⟨0, ?_⟩
      rw [Function.iterate_zero_apply]
      exact ⟨(hmeminv x hn'.2).mp hn'.1, hTc x hn'.2⟩
    · refine ⟨k, ?_⟩
      rw [Function.iterate_succ_apply] at hn
      exact hn
  refine ⟨B, hBmeas, Set.Subset.antisymm hsub1 hsub2, ?_⟩
  have hAB : A \ B ⊆ N := by
    intro x hx
    by_contra hxN
    have hxB : x ∈ B := by
      rw [hmemB x]
      exact ⟨0, by rw [Function.iterate_zero_apply]; exact ⟨hx.1, hxN⟩⟩
    exact hx.2 hxB
  have hBA : B \ A ⊆ N := by
    intro x hx
    by_contra hxN
    obtain ⟨n, hn⟩ := (hmemB x).mp hx.1
    exact hx.2 ((hconst n x hxN).mpr hn.1)
  exact measure_union_null (measure_mono_null hAB hNnull) (measure_mono_null hBA hNnull)

end Work.EKLC6Core
