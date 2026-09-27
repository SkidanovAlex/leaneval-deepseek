import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs

open MeasureTheory

namespace Work.EKLComp

set_option linter.unusedVariables false

/-!
# `FrozenBadSet ⊆ BadSet`

The frozen (Bochner-integral) form of the bad condition implies the `ℝ≥0∞` (lintegral) form.

Suppose `α * (ν x s).toReal < ∫_s f(g • x) dν x` for `s = ballU hij r`, `r > 0`.  Since `f ≥ 0`
and `α > 0`, the right-hand side is `> 0`; the Bochner integral is related to the lintegral by
`integral_eq_lintegral_of_nonneg_ae`, and `ofReal (α * M) = ofReal α * ofReal M = ofReal α * ν x s`
whenever the ball has finite `ν x`-measure (`hfin`).  Taking `ENNReal.ofReal` of the strict
inequality and using `ofReal_toReal_le` gives the `BadENN` condition.  (If the integrand is not
`AEStronglyMeasurable`, the Bochner integral is `0` by `integral_non_aestronglyMeasurable`, which
contradicts the hypothesis, so that case is vacuous.)
-/
theorem frozen_subset_bad (i j : Fin 3) (hij : i ≠ j)
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (α : ℝ) (hα : 0 < α)
    (x : Work.EKLContract.X3)
    (hfin : ∀ r : ℝ, 0 < r → ν x (Work.EKLContract.ballU hij r) ≠ ⊤) :
    x ∈ Work.EKLComp.FrozenBadSet i j hij ν f α → x ∈ Work.EKLComp.BadSet i j hij ν f α := by
  rintro ⟨r, hr, hlt⟩
  refine ⟨r, hr, ?_⟩
  show ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij r)
      < ∫⁻ g in Work.EKLContract.ballU hij r, ENNReal.ofReal (f (g • x)) ∂(ν x)
  by_cases hmeas : AEStronglyMeasurable (fun g : Work.EKLContract.SL3 => f (g • x))
      ((ν x).restrict (Work.EKLContract.ballU hij r))
  · have hFnn : 0 ≤ᵐ[(ν x).restrict (Work.EKLContract.ballU hij r)]
        (fun g : Work.EKLContract.SL3 => f (g • x)) :=
      Filter.Eventually.of_forall fun g => hf0 (g • x)
    have hconv := integral_eq_lintegral_of_nonneg_ae hFnn hmeas
    rw [hconv] at hlt
    have hMnn : (0 : ℝ) ≤ α * (ν x (Work.EKLContract.ballU hij r)).toReal :=
      mul_nonneg hα.le ENNReal.toReal_nonneg
    have hpos : (0 : ℝ) <
        (∫⁻ g, ENNReal.ofReal (f (g • x))
          ∂((ν x).restrict (Work.EKLContract.ballU hij r))).toReal :=
      lt_of_le_of_lt hMnn hlt
    have h1 : ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij r)
        = ENNReal.ofReal (α * (ν x (Work.EKLContract.ballU hij r)).toReal) := by
      rw [ENNReal.ofReal_mul hα.le, ENNReal.ofReal_toReal (hfin r hr)]
    calc ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij r)
        = ENNReal.ofReal (α * (ν x (Work.EKLContract.ballU hij r)).toReal) := h1
      _ < ENNReal.ofReal
            ((∫⁻ g, ENNReal.ofReal (f (g • x))
                ∂((ν x).restrict (Work.EKLContract.ballU hij r))).toReal) :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlt
      _ ≤ ∫⁻ g, ENNReal.ofReal (f (g • x))
            ∂((ν x).restrict (Work.EKLContract.ballU hij r)) := ENNReal.ofReal_toReal_le
  · exfalso
    have hzero : ∫ g, f (g • x) ∂((ν x).restrict (Work.EKLContract.ballU hij r)) = 0 :=
      integral_non_aestronglyMeasurable hmeas
    rw [hzero] at hlt
    have hMnn : (0 : ℝ) ≤ α * (ν x (Work.EKLContract.ballU hij r)).toReal :=
      mul_nonneg hα.le ENNReal.toReal_nonneg
    linarith

end Work.EKLComp
