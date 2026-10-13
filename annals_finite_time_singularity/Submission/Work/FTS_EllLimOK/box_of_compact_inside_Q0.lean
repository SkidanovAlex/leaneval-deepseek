import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

/-- A nonempty compact subset of the open quadrant `(0,∞) × (0,π/2)` sits inside a closed
rectangle `[a,b] × [c,d]` with `0 < a ≤ b`, `0 < c ≤ d` and `d < π/2`: take the extrema of
the (compact, hence nonempty) coordinate projections, which therefore stay in the open
quadrant. -/
theorem box_of_compact_inside_Q0 {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) (hne : K.Nonempty) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < Real.pi / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hKc1 : IsCompact (Prod.fst '' K) := hKc.image continuous_fst
  have hKc2 : IsCompact (Prod.snd '' K) := hKc.image continuous_snd
  have hne1 : (Prod.fst '' K).Nonempty := hne.image Prod.fst
  have hne2 : (Prod.snd '' K).Nonempty := hne.image Prod.snd
  obtain ⟨a, ha, hamin⟩ := hKc1.exists_isMinOn hne1 continuousOn_id
  obtain ⟨b, hb, hbmax⟩ := hKc1.exists_isMaxOn hne1 continuousOn_id
  obtain ⟨c, hc, hcmin⟩ := hKc2.exists_isMinOn hne2 continuousOn_id
  obtain ⟨d, hd, hdmax⟩ := hKc2.exists_isMaxOn hne2 continuousOn_id
  have hapos : 0 < a := by
    obtain ⟨p, hp, rfl⟩ := ha
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).1
  have hcpos : 0 < c := by
    obtain ⟨p, hp, rfl⟩ := hc
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).2.1
  have hdlt : d < Real.pi / 2 := by
    obtain ⟨p, hp, rfl⟩ := hd
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).2.2
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₀₁ : p₀.1 ∈ Prod.fst '' K := ⟨p₀, hp₀, rfl⟩
  have hp₀₂ : p₀.2 ∈ Prod.snd '' K := ⟨p₀, hp₀, rfl⟩
  refine ⟨a, b, c, d, hapos, ?_, hcpos, ?_, hdlt, ?_⟩
  · exact le_trans (hamin hp₀₁) (hbmax hp₀₁)
  · exact le_trans (hcmin hp₀₂) (hdmax hp₀₂)
  · intro p hp
    have hp1 : p.1 ∈ Prod.fst '' K := ⟨p, hp, rfl⟩
    have hp2 : p.2 ∈ Prod.snd '' K := ⟨p, hp, rfl⟩
    exact ⟨⟨hamin hp1, hbmax hp1⟩, ⟨hcmin hp2, hdmax hp2⟩⟩

end Work.FTS_EllLimOK
