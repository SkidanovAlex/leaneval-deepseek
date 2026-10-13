import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pw_identity_mine` — the pulled-back integrated identity

The pull-back of the integral identity `w_k(τ₂) − w_k(τ₁) = ∫(R_k − (Vz·wz_k + b·wθ_k))`
to `φ_k = w_k/om` in the logarithmic coordinates, with the pulled-back coefficients
`coefA Vz`, `coefB b`, `coefC α Vz b` and source `srcF α (R k)`.  Immediate from the
algebraic core `pw_alg` together with the constant-`om` pull-out `integral_div`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory
namespace Work.FTS_RegExport.RXT.Sys

theorem pw_identity_mine {n : ℕ} {w wz wθ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {Vz b : ℝ → ℝ → ℝ → ℝ} {S α : ℝ} (hα : 0 < α)
    (hId : ∀ k z θ τ₁ τ₂, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      w k z θ τ₂ - w k z θ τ₁
        = ∫ σ in τ₁..τ₂, (R k z θ σ - (Vz z θ σ * wz k z θ σ + b z θ σ * wθ k z θ σ))) :
    ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      pw α (w k) s ψ τ₂ - pw α (w k) s ψ τ₁
        = ∫ σ in τ₁..τ₂, (srcF α (R k) s ψ σ
            - (coefA Vz s ψ σ * pws α (wz k) (w k) s ψ σ
              + coefB b s ψ σ * pwψ α (wθ k) (w k) s ψ σ
              + coefC α Vz b s ψ σ * pw α (w k) s ψ σ)) := by
  intro k s ψ τ₁ τ₂ h1 h2 h3
  have hO : om α s ψ ≠ 0 := ne_of_gt (om_pos (α := α) hα)
  have hL : pw α (w k) s ψ τ₂ - pw α (w k) s ψ τ₁
      = (w k (cz s) (cth ψ) τ₂ - w k (cz s) (cth ψ) τ₁) / om α s ψ := by
    simp only [pw]
    field_simp
  rw [hL, hId k (cz s) (cth ψ) τ₁ τ₂ (cz_pos s) (cth_pos ψ) (cth_lt ψ) h1 h2 h3,
    ← intervalIntegral.integral_div (om α s ψ)]
  refine intervalIntegral.integral_congr ?_
  intro σ _
  exact pw_alg (α := α) hα

end Work.FTS_RegExport.RXT.Sys
