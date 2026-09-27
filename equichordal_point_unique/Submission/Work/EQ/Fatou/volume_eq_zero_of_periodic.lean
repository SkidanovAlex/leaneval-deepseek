import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory Set

theorem volume_eq_zero_of_periodic {S : Set ℝ}
    (hper : ∀ θ : ℝ, θ + 2 * Real.pi ∈ S ↔ θ ∈ S)
    (h0 : MeasureTheory.volume (S ∩ Set.Ioc 0 (2 * Real.pi)) = 0) :
    MeasureTheory.volume S = 0 := by
  -- Write the period as `c = 2π`.
  set c : ℝ := 2 * Real.pi with hc
  have hc_pos : 0 < c := by rw [hc]; positivity
  -- `2π` is a period of the predicate `θ ↦ θ ∈ S`.
  have hper_f : Function.Periodic (fun θ : ℝ => θ ∈ S) c := by
    intro θ
    rw [hc]
    exact propext (hper θ)
  -- hence so is every integer multiple `n • c`.
  have hper_z : ∀ (n : ℤ) (θ : ℝ), θ + n • c ∈ S ↔ θ ∈ S := by
    intro n θ
    exact ((Function.Periodic.zsmul hper_f n) θ).to_iff
  -- `S` is the union of the translates of its trace on the fundamental domain `(0, c]`.
  have hcover : S = ⋃ n : ℤ, (fun x : ℝ => x + n • c) '' (S ∩ Set.Ioc 0 c) := by
    apply le_antisymm
    · intro θ hθ
      rw [Set.mem_iUnion]
      -- the intervals `Ioc (n • c) ((n+1) • c)` cover the line.
      have hθ' : θ ∈ (⋃ n : ℤ, Set.Ioc (n • c) ((n + 1) • c) : Set ℝ) := by
        rw [iUnion_Ioc_zsmul hc_pos]; exact Set.mem_univ θ
      rw [Set.mem_iUnion] at hθ'
      obtain ⟨n, hn⟩ := hθ'
      refine ⟨n, θ - n • c, ⟨?_, ?_⟩, ?_⟩
      · exact (hper_z n (θ - n • c)).mp (by simpa using hθ)
      · rw [Set.mem_Ioc]
        constructor
        · simpa using sub_pos.mpr hn.1
        · have hle : θ ≤ n • c + c := by simpa [add_smul, one_smul] using hn.2
          exact sub_le_iff_le_add.mpr (by linarith [hle])
      · exact sub_add_cancel _ _
    · intro θ hθ
      rw [Set.mem_iUnion] at hθ
      obtain ⟨n, x, hx, hθx⟩ := hθ
      rw [← hθx]
      exact (hper_z n x).mpr hx.1
  rw [hcover]
  apply measure_iUnion_null
  intro n
  -- each translate of the null fundamental trace is again null.
  rw [Set.image_add_right, measure_preimage_add_right]
  simpa [hc] using h0

end Work.EQ.Fatou
