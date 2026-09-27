import Mathlib
import Submission.Work.EQ.SymDefs

namespace Work.EQ

/-- `LocalModel` is monotone in the radius parameter: shrinking `ε` preserves the model.
All the analytic estimates are phrased with `|ξ| ≤ 4 * ε`, hence hold a fortiori on the
smaller ball `|ξ| ≤ 4 * ε'` when `ε' ≤ ε`; the single arithmetic condition
`C * ε ≤ (1 - lam) / 4` weakens because `C > 0`. -/
theorem LocalModel_mono {T : ℂ → ℂ} {A : ℂ} {lam C ε ε' : ℝ} (h : LocalModel T A lam C ε)
    (hε'0 : 0 < ε') (hε'ε : ε' ≤ ε) : LocalModel T A lam C ε' := by
  obtain ⟨hAim, hε0, hC0, hlam0, hlam1, hCe, hreal, F, G, hFG, hFb, hGb, hFlip, hGlip⟩ := h
  have hCmono : C * ε' ≤ C * ε := mul_le_mul_of_nonneg_left hε'ε (le_of_lt hC0)
  have h4 : 4 * ε' ≤ 4 * ε := by linarith
  refine ⟨hAim, hε'0, hC0, hlam0, hlam1, ?_, ?_, F, G, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · intro ξ hξ
    exact hreal ξ (le_trans hξ h4)
  · intro ξ η hξ hη
    exact hFG ξ η (le_trans hξ h4) (le_trans hη h4)
  · intro ξ η hξ hη
    exact hFb ξ η (le_trans hξ h4) (le_trans hη h4)
  · intro ξ η hξ hη
    exact hGb ξ η (le_trans hξ h4) (le_trans hη h4)
  · intro ξ η ξ' η' hξ hη hξ' hη'
    exact hFlip ξ η ξ' η' (le_trans hξ h4) (le_trans hη h4) (le_trans hξ' h4) (le_trans hη' h4)
  · intro ξ η ξ' η' hξ hη hξ' hη'
    exact hGlip ξ η ξ' η' (le_trans hξ h4) (le_trans hη h4) (le_trans hξ' h4) (le_trans hη' h4)

end Work.EQ
