import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

/-- Oddness of `PhiOdd` in `θ`, with the vanishing hypothesis of `Φ` at `θ = 0` required only at
the positive point `w` at which the identity is evaluated.

This is `Work.FTS.BSIdent.PhiOdd_neg_theta` with a weakened hypothesis: the only case of the
case analysis in which `Φ` is evaluated at `θ = 0` is `θ = 0`, and there the first coordinate is
`w` (else `Φ` is evaluated at `±θ` with `θ ≠ 0`). -/
theorem PhiOdd_neg_theta_of_pos {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0) {w θ : ℝ} (hw : 0 < w) :
    Work.FTS.BSIdent.PhiOdd Φ w (-θ) τ = -Work.FTS.BSIdent.PhiOdd Φ w θ τ := by
  by_cases h : 0 ≤ θ
  · by_cases h' : 0 ≤ -θ
    · have hθ0 : θ = 0 := le_antisymm (by linarith) h
      subst hθ0
      simp [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 w hw]
    · rw [Work.FTS.BSIdent.PhiOdd_of_neg h', Work.FTS.BSIdent.PhiOdd_of_nonneg h, neg_neg]
  · have hpos : 0 ≤ -θ := by linarith
    rw [Work.FTS.BSIdent.PhiOdd_of_neg h, Work.FTS.BSIdent.PhiOdd_of_nonneg hpos, neg_neg]

end Work.FTS.BSIdent.Cyl.DecayAux
