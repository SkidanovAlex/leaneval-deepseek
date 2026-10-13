import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem exists_phi_ge_near_ends (φ : ℝ → ℝ) (C : ℝ)
    (h0 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε → B ≤ φ θ)
    (h1 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, Real.pi / 2 - ε < θ → θ < Real.pi / 2 → B ≤ φ θ) :
    ∃ a : ℝ, 0 < a ∧ a < Real.pi / 2 ∧
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → (θ < a ∨ Real.pi / 2 - a < θ) → C ≤ φ θ := by
  obtain ⟨e0, he0pos, he0⟩ := h0 C
  obtain ⟨e1, he1pos, he1⟩ := h1 C
  refine ⟨min (e0 / 2) (min (e1 / 2) (Real.pi / 4)), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (by linarith) (by positivity))
  · have hle : min (e0 / 2) (min (e1 / 2) (Real.pi / 4)) ≤ Real.pi / 4 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  · intro θ hθ hcase
    rcases hcase with hcase | hcase
    · have hlt : θ < e0 := by
        have h2 : θ < e0 / 2 := lt_of_lt_of_le hcase (min_le_left _ _)
        linarith
      exact he0 θ hθ.1 hlt
    · have hlt : Real.pi / 2 - e1 < θ := by
        have ha : min (e0 / 2) (min (e1 / 2) (Real.pi / 4)) ≤ e1 / 2 :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
      exact he1 θ hlt hθ.2

end Work.FTS_StreamBdry.SB25
