import Mathlib

open scoped Topology

namespace Work.Smooth.Morse.MorseModel

/-- If `g : X → ℝ → ℝ` is jointly continuous, is strictly monotone on `[0,1]` in its second
variable for every `x`, and `τ x ∈ [0,1]` is the (unique) point with `g x (τ x) = c`, then `τ`
is continuous. -/
theorem continuous_of_strictMonoOn_solution {X : Type*} [TopologicalSpace X] {g : X → ℝ → ℝ}
    (hg : Continuous (Function.uncurry g)) (hmono : ∀ x, StrictMonoOn (g x) (Set.Icc 0 1))
    {c : ℝ} {τ : X → ℝ} (hmem : ∀ x, τ x ∈ Set.Icc 0 1) (hτ : ∀ x, g x (τ x) = c) :
    Continuous τ := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_order]
  constructor
  · -- lower bounds:  a < τ x₀  ⟹  eventually  a < τ x
    intro a ha
    by_cases ha0 : a < 0
    · filter_upwards with x using lt_of_lt_of_le ha0 (hmem x).1
    · have ha0' : 0 ≤ a := not_lt.mp ha0
      have ha_le_one : a ≤ 1 := le_of_lt (lt_of_lt_of_le ha (hmem x₀).2)
      have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0', ha_le_one⟩
      have hgt : g x₀ a < c := by
        simpa [hτ x₀] using (hmono x₀) ha_mem (hmem x₀) ha
      have hcont : Continuous (fun x => g x a) := by
        have hφ : Continuous (fun x : X => (x, a)) := continuous_id.prodMk continuous_const
        exact hg.comp hφ
      have hkey : ∀ᶠ x in 𝓝 x₀, g x a < c :=
        hcont.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hgt)
      filter_upwards [hkey] with x hx
      have hle : g x (τ x) ≤ g x a ↔ τ x ≤ a := (hmono x).le_iff_le (hmem x) ha_mem
      have hnot : ¬ (g x (τ x) ≤ g x a) := by rw [hτ x]; exact not_le.mpr hx
      exact not_le.mp (hle.not.mp hnot)
  · -- upper bounds:  τ x₀ < a  ⟹  eventually  τ x < a
    intro a ha
    by_cases ha1 : 1 < a
    · filter_upwards with x using lt_of_le_of_lt (hmem x).2 ha1
    · have ha1' : a ≤ 1 := not_lt.mp ha1
      have ha_pos : 0 < a := lt_of_le_of_lt (hmem x₀).1 ha
      have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ha_pos, ha1'⟩
      have hgt : c < g x₀ a := by
        simpa [hτ x₀] using (hmono x₀) (hmem x₀) ha_mem ha
      have hcont : Continuous (fun x => g x a) := by
        have hφ : Continuous (fun x : X => (x, a)) := continuous_id.prodMk continuous_const
        exact hg.comp hφ
      have hkey : ∀ᶠ x in 𝓝 x₀, c < g x a :=
        hcont.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
      filter_upwards [hkey] with x hx
      have hle : g x a ≤ g x (τ x) ↔ a ≤ τ x := (hmono x).le_iff_le ha_mem (hmem x)
      have hnot : ¬ (g x a ≤ g x (τ x)) := by rw [hτ x]; exact not_le.mpr hx
      exact not_le.mp (hle.not.mp hnot)

end Work.Smooth.Morse.MorseModel
