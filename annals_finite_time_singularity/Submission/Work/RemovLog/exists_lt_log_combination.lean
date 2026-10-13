import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RemovLog

/-- For `a < b` and `μ > 0`, taking `t` close enough to `b` from the left makes
`K + μ * log (b - t)` arbitrarily negative. -/
theorem exists_lt_log_combination {a b K μ M : ℝ} (hab : a < b) (hμ : 0 < μ) :
    ∃ t ∈ Set.Ioo a b, K + μ * Real.log (b - t) < M := by
  have hgap : 0 < b - a := by linarith
  have hexp : 0 < Real.exp ((M - K) / μ) := Real.exp_pos _
  have hle : min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) < b - a :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlt : min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2)
      < Real.exp ((M - K) / μ) :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hpos : 0 < min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) :=
    lt_min (by linarith) (by linarith)
  refine ⟨b - min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2), ?_, ?_⟩
  · constructor
    · linarith
    · linarith
  · have hb : b - (b - min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2))
        = min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) := by ring
    rw [hb]
    set δ := min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) with hδdef
    have hδpos : 0 < δ := hpos
    have hδexp : δ < Real.exp ((M - K) / μ) := hlt
    have hlog : Real.log δ < (M - K) / μ := by
      have h1 := Real.log_lt_log hδpos hδexp
      rwa [Real.log_exp] at h1
    have h4 : μ * ((M - K) / μ) = M - K := by field_simp
    have h3 := mul_lt_mul_of_pos_left hlog hμ
    linarith [h3, h4]

end Work.RemovLog
