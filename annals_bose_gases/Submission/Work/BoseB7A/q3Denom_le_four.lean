import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7A.PH_subset_PHq_sub
import Submission.Work.BoseB7A.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7A

theorem q3Denom_le_four (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.q3Denom s k ≤ 4 := by
  obtain ⟨t₁, ht₁, h₁⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := kernel_basic K₀ b₀ hb₀
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK s k hfL hk
  have hle₁ : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have hle₂ : hv.t ≤ t₂ := le_trans htle (min_le_right _ _)
  obtain ⟨hPHq, hsubq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨-, -, hα, -, -⟩ := h₂ F T E hv hle₂ hb hK
  have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := hPHq k hkPH
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsubq s k hfL hk
  have hk := hα k hqk
  have hsk := hα (s - k) hqsk
  show 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2)) ≤ 4
  have hden : (1 / 2 : ℝ) * (1 / 2) ≤ (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) :=
    mul_le_mul hk hsk (by norm_num) (by linarith)
  calc 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2))
      ≤ 1 / ((1 / 2 : ℝ) * (1 / 2)) :=
        one_div_le_one_div_of_le (by norm_num) hden
    _ = 4 := by norm_num

end Work.BoseB7A
