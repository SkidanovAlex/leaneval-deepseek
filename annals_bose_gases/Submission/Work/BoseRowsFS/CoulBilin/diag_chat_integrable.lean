import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.C3Q.coulomb_W1fun_le
import Submission.Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq
import Submission.Work.BoseBogFS.continuous_chat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.CoulBilin

/-- **Finiteness of the Coulomb double `∫⁻` forces integrability of the diagonal momentum
integrand `Ŵ(k)²/(2‖k‖²)`.**

Here `Ŵ = Work.BoseFixR.chat W` is the `p`-convention Fourier transform.  The plain diagonal
identity (`Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq`, for pointwise nonnegative even integrable
`W`) gives

  `∫⁻ k, ofReal (Ŵ(k)²/‖k‖²) = ofReal (2π²) · X2 W W`,

which is finite exactly when `X2 W W ≠ ⊤`; the `1/2` in the denominator only decreases the
integrand, so `∫⁻ k, ofReal (Ŵ(k)²/(2‖k‖²)) ≠ ⊤` as well.  Since `Ŵ` is continuous
(`Work.BoseBogFS.continuous_chat`) and the integrand is pointwise nonnegative,
`MeasureTheory.hasFiniteIntegral_iff_ofReal` turns that into `Integrable`. -/
theorem diag_chat_integrable {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤) :
    MeasureTheory.Integrable
      (fun k : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chat W k ^ 2 / (2 * ‖k‖ ^ 2)) := by
  -- The un-halved diagonal `∫⁻` is finite, by the Coulomb identity and the hypothesis.
  have hkey : (∫⁻ p, ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / ‖p‖ ^ 2)) ≠ ⊤ := by
    rw [Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq hW hW0 hWe]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  -- Halving the denominator only decreases the integrand, pointwise.
  have hmono : (∫⁻ k, ENNReal.ofReal (Work.BoseFixR.chat W k ^ 2 / (2 * ‖k‖ ^ 2)))
      ≤ (∫⁻ p, ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / ‖p‖ ^ 2)) := by
    apply MeasureTheory.lintegral_mono
    intro k
    apply ENNReal.ofReal_le_ofReal
    rcases eq_or_lt_of_le (norm_nonneg k) with h | h
    · -- `k = 0`: both quotients vanish (`x / 0 = 0` in `ℝ`).
      rw [← h]
      simp
    · have h2 : (0 : ℝ) < ‖k‖ ^ 2 := pow_pos h 2
      have h3 : ‖k‖ ^ 2 ≤ 2 * ‖k‖ ^ 2 := by linarith
      exact div_le_div_of_nonneg_left (sq_nonneg _) h2 h3
  have hne : (∫⁻ k, ENNReal.ofReal (Work.BoseFixR.chat W k ^ 2 / (2 * ‖k‖ ^ 2))) ≠ ⊤ :=
    ne_top_of_le_ne_top hkey hmono
  refine ⟨?_, ?_⟩
  · -- Measurability: `Ŵ` is continuous, so the quotient is measurable.
    have hc : Continuous (Work.BoseFixR.chat W) := Work.BoseBogFS.continuous_chat W hW
    have hm : Measurable (fun k : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.chat W k ^ 2 / (2 * ‖k‖ ^ 2)) :=
      (hc.measurable.pow_const 2).div
        (measurable_const.mul (continuous_norm.measurable.pow_const 2))
    exact hm.aestronglyMeasurable
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun k => by positivity))]
    exact lt_top_iff_ne_top.mpr hne

end Work.BoseRowsFS.CoulBilin
