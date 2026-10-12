import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.View
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open Work.BoseFixR

/-- On the low band `‖k‖ ≤ c₁ ≤ 4K_L√(μa)` the UV cut-off `ζ_Λ` is `1` (its radius `Λ`
satisfies `Λ ≥ 4K_L√(μa)`), so `E.W1` agrees there with `chat (W1fun v h (ell v μ))`, and the
ball hypothesis `hball` transfers. -/
theorem W1_lowband_viewFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {gHat0 : ℝ} (hview : Work.BoseBogFS.RViewFS v h μ F T E gHat0) {c₁ w₀ : ℝ}
    (hκ : 0 < E.KL * Real.sqrt (E.mu * E.aScat))
    (hc₁ : c₁ ≤ 4 * (E.KL * Real.sqrt (E.mu * E.aScat)))
    (hball : ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ≤ c₁ →
      w₀ ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) k) :
    ∀ k : Mode, ‖F.kmom k‖ ≤ c₁ → w₀ ≤ E.W1 k := by
  intro k hk
  obtain ⟨fu, Λ, hΛ, hW1⟩ := hview.W1_pin
  have hΛpos : 0 < Λ := lt_of_lt_of_le (mul_pos (by norm_num) hκ) hΛ
  have hkΛ : ‖F.kmom k‖ ≤ Λ := le_trans hk (le_trans hc₁ hΛ)
  have hζ : uvCut fu Λ (F.kmom k) = 1 := by
    rw [uvCut]
    exact fu.one _ ((div_le_one hΛpos).mpr hkΛ)
  have hW1k : E.W1 k = uvCut fu Λ (F.kmom k) * chat (W1fun v h (ell v μ)) (F.kmom k) := by
    simp only [hW1]
  rw [hW1k, hζ, one_mul]
  exact hball (F.kmom k) hk

end Work.BoseBogFS
