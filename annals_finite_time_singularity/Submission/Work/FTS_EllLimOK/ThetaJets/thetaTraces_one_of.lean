import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaJets.thetaTraces_one_of` (lead install R6, 2026-10-11)

`ThetaTraces α k g → ThetaTraces 1 k g` for `α ≥ 1`: `γ(1) ≤ γ(α)`, so on `sin 2θ ∈ (0,1]`,
`sin^{1-γ(1)} ≤ sin^{1-γ(α)}` (the θ-part of `bdryTraces_one_of`).  Feeds the `thTr` field in
`classC_one_of` (`ThetaJets/ClassC_le.lean`).
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS_EllLimOK.ThetaJets

theorem thetaTraces_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (htr : Work.FTS.PhiStar.ThetaTraces α k g) : Work.FTS.PhiStar.ThetaTraces 1 k g := by
  intro s hs z hz
  obtain ⟨h3, h4⟩ := htr s hs z hz
  have hgam : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.gam]; linarith
  constructor
  · refine squeeze_zero' ?_ ?_ h3
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)
  · refine squeeze_zero' ?_ ?_ h4
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)

end Work.FTS_EllLimOK.ThetaJets
