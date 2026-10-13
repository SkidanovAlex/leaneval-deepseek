import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem sin_two_lower_bound_rect {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ m : ℝ, 0 < m ∧ ∀ θ ∈ Set.Icc c d, m ≤ Real.sin (2 * θ) := by
  rcases le_or_gt c d with hcd | hdc
  · -- nonempty rectangle: the minimum of `sin(2·)` on `[c,d]` is attained at an endpoint
    have hdpos : 0 < d := lt_of_lt_of_le hc hcd
    refine ⟨min (Real.sin (2 * c)) (Real.sin (2 * d)), lt_min ?_ ?_, ?_⟩
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    · intro θ hθ
      rw [Set.mem_Icc] at hθ
      obtain ⟨hcθ, hθd⟩ := hθ
      rcases le_or_gt (2 * θ) (Real.pi / 2) with hcase | hcase
      · -- `2θ ≤ π/2`: `sin` is increasing on `[-(π/2), π/2]`
        have hmono : Real.sin (2 * c) ≤ Real.sin (2 * θ) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 2 * c)
            hcase (by linarith)
        exact le_trans (min_le_left _ _) hmono
      · -- `π/2 ≤ 2θ`: `sin x = cos (x - π/2)` with `cos` decreasing on `[0, π]`
        have hmono : Real.cos (2 * d - Real.pi / 2) ≤ Real.cos (2 * θ - Real.pi / 2) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * θ - Real.pi / 2)
            (y := 2 * d - Real.pi / 2) (by linarith) (by linarith) (by linarith)
        have hsin : Real.sin (2 * d) ≤ Real.sin (2 * θ) := by
          rw [← Real.cos_sub_pi_div_two (2 * d), ← Real.cos_sub_pi_div_two (2 * θ)]
          exact hmono
        exact le_trans (min_le_right _ _) hsin
  · -- the rectangle is empty, so any positive constant works
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact absurd (le_trans hθ.1 hθ.2) (not_le.mpr hdc)

end Work.FTS.StrongEps.LocUnif
