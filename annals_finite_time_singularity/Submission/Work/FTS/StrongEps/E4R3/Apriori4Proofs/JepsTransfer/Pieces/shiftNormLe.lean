/-
# `shiftNormLe` — the weighted `L²` norm is shifted by at most `e^{Cw |p|}`

This file proves the elementary shift estimate for the weight `Q` on the plane
`ℝ × ℝ` (in the application `Q` is a leaf weight of the polar/log coordinates and
`G` is a function whose weighted `L²` norm is finite).

If `Q (y + p) ≤ e^{Cw (|p₁| + |p₂|)} Q y` for all `y, p` and `Q ≥ 0`, then
substituting `y ↦ y - p` gives the *reverse* one-sided bound

  `Q y ≤ e^{Cw |p|} Q (y - p)`,

i.e. `Q` *grows* by at most `e^{Cw |p|}` when shifted backwards.  Multiplying by
`G (y - p)²` and integrating, translation invariance of Lebesgue measure on `ℝ × ℝ`
(`MeasureTheory.integral_sub_right_eq_self`, available on `ℝ × ℝ` through the add-Haar
instance) turns this into the asserted shift bound for the weighted `L²` norm; the
same pointwise inequality with a translation-invariant dominating function gives the
integrability statement.  Note that only the one-sided hypothesis `hQsh` is needed:
the reverse inequality `Q y ≤ e^{Cw|p|} Q (y+p)` (a hypothesis in the sibling
`dabsIntLe`) is *not* used here.  Of the hypotheses, `hQ0` is used for the `‖·‖`
estimate in the integrability step, `hQm`/`hG` for measurability, and `hI` for
finiteness; `hCw` (`0 ≤ Cw`) is not needed by the argument, since `Real.exp` is
positive unconditionally — it is kept because it is part of the caller's interface.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

set_option linter.unusedVariables false in
theorem shiftNormLe {Q G : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG : Measurable G) (hI : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2))
    (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) ∧
      ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2
        ≤ Real.exp (Cw * (|p.1| + |p.2|)) * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by
  set c : ℝ := Real.exp (Cw * (|p.1| + |p.2|)) with hc
  -- the backwards shift bound on the weight
  have hQshift : ∀ y : ℝ × ℝ, Q y ≤ c * Q (y - p) := by
    intro y
    rw [hc]
    simpa using hQsh (y - p) p
  have hsub : Measurable fun y : ℝ × ℝ => y - p := measurable_id.sub measurable_const
  -- the shifted integrand, which is integrable by translation invariance
  have hH : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G (y - p) ^ 2) :=
    hI.comp_sub_right p
  have hcH : MeasureTheory.Integrable (fun y : ℝ × ℝ => c * (Q (y - p) * G (y - p) ^ 2)) :=
    hH.const_mul c
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) :=
    (hQm.mul ((hG.comp hsub).pow_const 2)).aestronglyMeasurable
  -- the pointwise comparison, both for the integral and (through `‖·‖`) for integrability
  have hle : ∀ y : ℝ × ℝ, Q y * G (y - p) ^ 2 ≤ c * (Q (y - p) * G (y - p) ^ 2) := by
    intro y
    have h := mul_le_mul_of_nonneg_right (hQshift y) (sq_nonneg (G (y - p)))
    calc Q y * G (y - p) ^ 2 ≤ (c * Q (y - p)) * G (y - p) ^ 2 := h
      _ = c * (Q (y - p) * G (y - p) ^ 2) := by ring
  have hnorm : ∀ y : ℝ × ℝ, ‖Q y * G (y - p) ^ 2‖ ≤ c * (Q (y - p) * G (y - p) ^ 2) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hQ0 y) (sq_nonneg (G (y - p))))]
    exact hle y
  have hFint : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) :=
    hcH.mono' hFmeas (Filter.Eventually.of_forall hnorm)
  refine ⟨hFint, ?_⟩
  calc ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2
      ≤ ∫ y : ℝ × ℝ, c * (Q (y - p) * G (y - p) ^ 2) :=
        MeasureTheory.integral_mono hFint hcH hle
    _ = c * ∫ y : ℝ × ℝ, Q (y - p) * G (y - p) ^ 2 :=
        MeasureTheory.integral_const_mul c (fun y : ℝ × ℝ => Q (y - p) * G (y - p) ^ 2)
    _ = c * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by
        congr 1
        exact MeasureTheory.integral_sub_right_eq_self (fun y : ℝ × ℝ => Q y * G y ^ 2) p
    _ = Real.exp (Cw * (|p.1| + |p.2|)) * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by rw [hc]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
