import Mathlib

namespace Work.EKLC6Core

open MeasureTheory Filter

/-- Shifting the index of a `ℕ`-indexed `atTop`-frequently statement by one:
`∃ᶠ n, p n` iff `∃ᶠ n, p (n+1)`. -/
private theorem frequently_atTop_add_one {p : ℕ → Prop} :
    (∃ᶠ n in Filter.atTop, p n) ↔ (∃ᶠ n in Filter.atTop, p (n + 1)) := by
  have h := Filter.frequently_map (f := Filter.atTop) (m := fun n : ℕ => n + 1) (P := p)
  rwa [Filter.map_add_atTop_eq_nat 1] at h

theorem ae_frequently_mem_of_pos_measure {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasureTheory.MeasurePreserving T μ μ)
    (herg : ∀ E : Set X, MeasurableSet E → T ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    {G : Set X} (hG : MeasurableSet G) (hpos : 0 < μ G) :
    ∀ᵐ x ∂μ, ∃ᶠ n in Filter.atTop, (T^[n]) x ∈ G := by
  -- a measure preserving self-map of a finite measure space is conservative,
  -- so the Poincaré recurrence theorem applies to it.
  have hcons : MeasureTheory.Conservative T μ := hT.conservative
  -- `A` is the set of points whose orbit visits `G` infinitely often.
  let A : Set X := {x | ∃ᶠ n in Filter.atTop, T^[n] x ∈ G}
  have hAmeas : MeasurableSet A := by
    show MeasurableSet {x : X | ∃ᶠ n in Filter.atTop, T^[n] x ∈ G}
    have hEq : {x : X | ∃ᶠ n in Filter.atTop, T^[n] x ∈ G}
        = ⋂ N, ⋃ n ∈ Set.Ici N, (T^[n]) ⁻¹' G := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_Ici, Filter.frequently_atTop, exists_prop]
    rw [hEq]
    exact MeasurableSet.iInter fun N =>
      MeasurableSet.biUnion (Set.to_countable _) fun n _ => (hT.measurable.iterate n) hG
  -- `A` is invariant under `T` (indeed, exactly, so a fortiori a.e.).
  have hshift : ∀ x : X, (∃ᶠ n in Filter.atTop, T^[n] (T x) ∈ G) ↔
      (∃ᶠ n in Filter.atTop, T^[n] x ∈ G) := by
    intro x
    have h := (frequently_atTop_add_one (p := fun k => T^[k] x ∈ G)).symm
    simpa [Function.iterate_succ_apply] using h
  have hAinv : T ⁻¹' A =ᵐ[μ] A := by
    have hset : T ⁻¹' A = A := by
      ext x
      simp only [Set.mem_preimage, A, Set.mem_ofPred_eq]
      exact hshift x
    rw [hset]
    all_goals exact Filter.EventuallyEq.rfl
  rcases herg A hAmeas hAinv with h0 | hc
  · -- `μ A ≠ 0` by Poincaré recurrence, so this case is impossible.
    exfalso
    have hAG_eq : μ (G ∩ A) = μ G :=
      hcons.measure_inter_frequently_image_mem_eq hG.nullMeasurableSet
    have hle : μ G ≤ μ A := by
      rw [← hAG_eq]
      exact MeasureTheory.measure_mono Set.inter_subset_right
    rw [h0] at hle
    exact hpos.not_ge hle
  · -- `μ Aᶜ = 0` is exactly the statement to prove.
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hc] with x hx
    have hx' : x ∈ A := by simpa using hx
    simpa [A, Set.mem_ofPred_eq] using hx'

end Work.EKLC6Core
