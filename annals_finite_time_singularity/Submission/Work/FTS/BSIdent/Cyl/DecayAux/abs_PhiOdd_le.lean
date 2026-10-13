import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem abs_PhiOdd_le {Φ : Work.FTS.BSIdent.Fam} {τ C₀ q lam : ℝ} (hC₀ : 0 ≤ C₀)
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ| ≤ C₀ * (Real.pi / 2 - |θ|) ^ q * (1 + w) ^ (-lam) := by
  rcases lt_trichotomy θ 0 with hneg | hzero | hpos
  · rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hneg), abs_neg, abs_of_neg hneg]
    exact hrate w (-θ) hw (neg_pos.mpr hneg) (by rw [abs_of_neg hneg] at hθ; exact hθ)
  · subst hzero
    rw [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 w hw, abs_zero]
    exact mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (by linarith [Real.pi_pos]) q))
      (le_of_lt (Real.rpow_pos_of_pos (by linarith) (-lam)))
  · rw [Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hpos), abs_of_pos hpos]
    exact hrate w θ hw hpos (by rwa [abs_of_pos hpos] at hθ)

end Work.FTS.BSIdent.Cyl.DecayAux
