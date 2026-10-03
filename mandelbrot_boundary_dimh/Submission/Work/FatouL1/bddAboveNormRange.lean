import Mathlib

namespace Work.FatouL1

theorem bddAboveNormRange {f : ℝ → ℂ} (hcont : Continuous f)
    (htop : Filter.Tendsto f Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto f Filter.atBot (nhds 0)) :
    BddAbove (Set.range fun y : ℝ => ‖f y‖) := by
  have htop0 : Filter.Tendsto (fun y : ℝ => ‖f y‖) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.norm htop
  have hbot0 : Filter.Tendsto (fun y : ℝ => ‖f y‖) Filter.atBot (nhds 0) := by
    simpa using Filter.Tendsto.norm hbot
  have htop' : ∀ᶠ y in Filter.atTop, ‖f y‖ ≤ 1 :=
    (htop0.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).mono
      (fun y hy => le_of_lt hy)
  have hbot' : ∀ᶠ y in Filter.atBot, ‖f y‖ ≤ 1 :=
    (hbot0.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).mono
      (fun y hy => le_of_lt hy)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp htop'
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp hbot'
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := min a b) (b := max a b)).image
    hcont.norm |>.bddAbove
  refine ⟨max C 1, ?_⟩
  rintro x ⟨y, rfl⟩
  by_cases hy : a ≤ y
  · exact le_trans (ha y hy) (le_max_right _ _)
  · rw [not_le] at hy
    by_cases hy2 : y ≤ b
    · exact le_trans (hb y hy2) (le_max_right _ _)
    · rw [not_le] at hy2
      have hmem : y ∈ Set.Icc (min a b) (max a b) :=
        ⟨le_of_lt (lt_of_le_of_lt (min_le_right a b) hy2),
         le_of_lt (lt_of_lt_of_le hy (le_max_left a b))⟩
      exact le_trans (hC ⟨y, hmem, rfl⟩) (le_max_left _ _)

end Work.FatouL1
