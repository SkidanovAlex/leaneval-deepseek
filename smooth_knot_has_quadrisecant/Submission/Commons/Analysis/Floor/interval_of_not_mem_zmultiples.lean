import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Floor

theorem interval_of_not_mem_zmultiples {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    {f : α → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 < a)
    (h : ∀ x : α, f x ∉ AddSubgroup.zmultiples a) :
    ∃ k : ℤ, ∀ x : α, f x ∈ Set.Ioo ((k : ℝ) * a) (((k : ℝ) + 1) * a) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, fun x => (hα.false x).elim⟩
  · obtain ⟨x₀⟩ := hα
    have hs : IsPreconnected (Set.range f) := isPreconnected_range hf
    have hmem : ∀ y ∈ Set.range f, y ∉ AddSubgroup.zmultiples a := by
      rintro y ⟨z, rfl⟩
      exact h z
    let k : ℤ := ⌊f x₀ / a⌋
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hlow : (k : ℝ) * a < f x₀ := by
      have h1 : (k : ℝ) ≤ f x₀ / a := Int.floor_le (f x₀ / a)
      have h2 : (k : ℝ) * a ≤ (f x₀ / a) * a := mul_le_mul_of_nonneg_right h1 ha.le
      rw [div_mul_cancel₀ (f x₀) ha_ne] at h2
      refine lt_of_le_of_ne h2 ?_
      intro heq
      exact hmem ((k : ℝ) * a) ⟨x₀, heq.symm⟩ (AddSubgroup.intCast_mul_mem_zmultiples a k)
    have hupp : f x₀ < ((k : ℝ) + 1) * a := by
      have h1 : f x₀ / a < (k : ℝ) + 1 := Int.lt_floor_add_one (f x₀ / a)
      have h2 : (f x₀ / a) * a < ((k : ℝ) + 1) * a := mul_lt_mul_of_pos_right h1 ha
      rwa [div_mul_cancel₀ (f x₀) ha_ne] at h2
    refine ⟨k, fun x => ?_⟩
    rw [Set.mem_Ioo]
    constructor
    · by_contra hc
      push Not at hc
      have hrin : (k : ℝ) * a ∈ Set.range f :=
        hs.Icc_subset ⟨x, rfl⟩ ⟨x₀, rfl⟩ ⟨hc, hlow.le⟩
      exact hmem ((k : ℝ) * a) hrin (AddSubgroup.intCast_mul_mem_zmultiples a k)
    · by_contra hc
      push Not at hc
      have hrin : ((k : ℝ) + 1) * a ∈ Set.range f :=
        hs.Icc_subset ⟨x₀, rfl⟩ ⟨x, rfl⟩ ⟨hupp.le, hc⟩
      have heq : ((k : ℝ) + 1) * a = ((k + 1 : ℤ) : ℝ) * a := by push_cast; ring
      refine hmem (((k : ℝ) + 1) * a) hrin ?_
      rw [heq]
      exact AddSubgroup.intCast_mul_mem_zmultiples a (k + 1)

end Commons.Analysis.Floor