import Mathlib

namespace Work.EKLC6Core

open MeasureTheory Filter

/-- Ergodicity of `T` w.r.t. `μ`, phrased as: every a.e.-invariant measurable set is null or
conull, implies that a.e. point visits a positive-measure measurable set `Y` infinitely often.

This is Poincaré recurrence combined with ergodicity: the set of points that visit `Y` infinitely
often is exactly `T`-invariant, and Poincaré recurrence shows it has positive measure (it contains
a.e. point of `Y`), so by ergodicity it is conull. -/
theorem good_time_freq {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasureTheory.MeasurePreserving T μ μ)
    (hErgT : ∀ E : Set X, MeasurableSet E → T ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    {Y : Set X} (hY : MeasurableSet Y) (hYpos : 0 < μ Y) :
    ∀ᵐ x ∂μ, ∃ᶠ n in Filter.atTop, (T^[n]) x ∈ Y := by
  classical
  -- The set of points whose orbit visits `Y` infinitely often.
  set B : Set X := {x | ∃ᶠ n in Filter.atTop, (T^[n]) x ∈ Y} with hBdef
  -- `B` is measurable, being a countable intersection of countable unions of preimages.
  have hBmeas : MeasurableSet B := by
    rw [hBdef]
    have h : {x | ∃ᶠ n in Filter.atTop, (T^[n]) x ∈ Y} =
        ⋂ a : ℕ, ⋃ b ∈ Set.Ici a, (T^[b]) ⁻¹' Y := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici,
        Set.mem_preimage]
      rw [frequently_atTop]
      constructor <;> intro h a
      · obtain ⟨b, hab, hb⟩ := h a; exact ⟨b, hab, hb⟩
      · obtain ⟨b, hab, hb⟩ := h a; exact ⟨b, hab, hb⟩
    rw [h]
    exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun _ => (hT.measurable.iterate b) hY
  -- `B` is `T`-invariant.
  have hBinv : T ⁻¹' B =ᵐ[μ] B := by
    have hEq : T ⁻¹' B = B := by
      rw [hBdef]
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      have h1 : ∀ n, (T^[n]) (T x) = (T^[n + 1]) x := by
        intro n
        rw [← Function.iterate_succ_apply T n x, Nat.succ_eq_add_one]
      simp only [h1]
      rw [frequently_atTop, frequently_atTop]
      constructor
      · intro h a
        obtain ⟨b, hab, hb⟩ := h a
        exact ⟨b + 1, le_trans hab (Nat.le_succ b), hb⟩
      · intro h a
        obtain ⟨c, hac, hc⟩ := h (a + 1)
        exact ⟨c - 1, by omega, by rwa [Nat.sub_add_cancel (by omega : 1 ≤ c)]⟩
    exact Filter.EventuallyEq.of_eq hEq
  -- `B` has positive measure: Poincaré recurrence gives that a.e. point of `Y` is in `B`.
  have hμBpos : 0 < μ B := by
    have hcons : MeasureTheory.Conservative T μ := hT.conservative
    have hYB : μ (Y ∩ B) = μ Y := by
      have := hcons.measure_inter_frequently_image_mem_eq hY.nullMeasurableSet
      simpa only [hBdef] using this
    have hle : μ Y ≤ μ B := by
      rw [← hYB]
      exact MeasureTheory.measure_mono Set.inter_subset_right
    exact lt_of_lt_of_le hYpos hle
  -- By ergodicity `μ B = 0` or `μ Bᶜ = 0`; positivity rules out the first case.
  rcases hErgT B hBmeas hBinv with hB0 | hBc0
  · exact absurd hB0 (ne_of_gt hμBpos)
  · rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hBc0
    simp only [Set.mem_compl_iff, not_not] at hBc0
    simpa only [hBdef, Set.mem_ofPred_eq] using hBc0

end Work.EKLC6Core
