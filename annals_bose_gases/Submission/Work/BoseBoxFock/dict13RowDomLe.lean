import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13RowDomLe` — the pointwise domination of the row integrand

The four rows of the `Q M Q` kernel `qmqKernel ℓ e` are bounded pointwise by the four box integrals
of `‖e‖` (`rowDom`, `dict13Aux`); multiplying by the (bounded) state factors gives the pointwise
domination of the `rowShape13` integrand by `rowDom`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

set_option autoImplicit false

/-- The norm of the coercion of a real number. -/
theorem enorm_ofReal_real (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]

/-- The pointwise bound of the `Q M Q` kernel by the four rows of the box `L¹` norm of `e`. -/
theorem qmqKernel_enorm_le {ℓ : ℝ} (hℓ : 0 < ℓ) (e : E3 → E3 → ℝ) (w y : E3) :
    ‖qmqKernel ℓ e w y‖ₑ
      ≤ ‖e w y‖ₑ
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹)
            * ∫⁻ y', ‖e w y'‖ₑ ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹)
            * ∫⁻ w', ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2
            * ∫⁻ w', ∫⁻ y', ‖e w' y'‖ₑ
                ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
                ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
  have hcoef : ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((ℓ ^ 3)⁻¹) := by
    rw [enorm_ofReal_real, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ℓ ^ 3))]
  have hcoef2 : ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ) ^ 2‖ₑ = ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2 := by
    rw [enorm_pow, hcoef]
  have key : ∀ f : E3 → ℝ,
      ‖(∫ z in Submission.BoseGases.acube ℓ, ((f z : ℝ) : ℂ))‖ₑ
        ≤ ∫⁻ z, ‖f z‖ₑ ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := fun f =>
    (enorm_integral_le_lintegral_enorm
      (fun z : E3 => ((f z : ℝ) : ℂ))).trans_eq
      (lintegral_congr fun z => enorm_ofReal_real (f z))
  have hB : ‖qmqRowB ℓ e w‖ₑ
      ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹)
        * ∫⁻ y', ‖e w y'‖ₑ ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    rw [qmqRowB, enorm_mul, hcoef]
    exact mul_le_mul' le_rfl (key _)
  have hC : ‖qmqRowC ℓ e y‖ₑ
      ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹)
        * ∫⁻ w', ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    rw [qmqRowC, enorm_mul, hcoef]
    exact mul_le_mul' le_rfl (key _)
  have hD : ‖qmqRowD ℓ e‖ₑ
      ≤ ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2
          * ∫⁻ w', ∫⁻ y', ‖e w' y'‖ₑ
              ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
              ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    rw [qmqRowD, enorm_mul, hcoef2]
    refine mul_le_mul' le_rfl ?_
    refine (enorm_integral_le_lintegral_enorm
      (fun w' : E3 => (∫ y' in Submission.BoseGases.acube ℓ, ((e w' y' : ℝ) : ℂ)))).trans ?_
    exact lintegral_mono fun w' => key (e w')
  rw [qmqKernel]
  refine (enorm_add_le _ _).trans (add_le_add ?_ hD)
  refine (enorm_sub_le.trans (add_le_add ?_ hC))
  exact (enorm_sub_le.trans (add_le_add (le_of_eq (enorm_ofReal_real (e w y))) hB))

/-- **The pointwise domination of the `rowShape13` integrand by `rowDom`.** -/
theorem rowProd_enorm_le_rowDom {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Xn n → ℂ}
    {A B : E3 → ℂ} {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (z : Xn n × (E3 × E3)) :
    ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ ≤ rowDom ℓ Θ A B p e z := by
  have hker := qmqKernel_enorm_le hℓ e (z.1 p.2) (z.2.1)
  have hstar : ∀ a : ℂ, ‖star a‖ₑ = ‖a‖ₑ := fun a => by simp [enorm_eq_nnnorm]
  have hfact : ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ
      = ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ * ‖qmqKernel ℓ e (z.1 p.2) (z.2.1)‖ₑ * ‖B z.2.2‖ₑ
        * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ := by
    simp only [rowProd, rowInt, enorm_mul, hstar]
  rw [hfact, rowDom]
  have hfac : ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ * ‖qmqKernel ℓ e (z.1 p.2) (z.2.1)‖ₑ * ‖B z.2.2‖ₑ
        * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ
      ≤ ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ * ‖B z.2.2‖ₑ
        * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ
        * (‖e (z.1 p.2) z.2.1‖ₑ
            + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
                ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
            + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ w', ‖e w' z.2.1‖ₑ
                ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
            + ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2
                * ∫⁻ w', ∫⁻ y', ‖e w' y'‖ₑ
                    ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
                    ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
    calc ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ * ‖qmqKernel ℓ e (z.1 p.2) (z.2.1)‖ₑ * ‖B z.2.2‖ₑ
          * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ
        ≤ ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ
            * (‖e (z.1 p.2) z.2.1‖ₑ
              + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
                  ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
              + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ w', ‖e w' z.2.1‖ₑ
                  ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
              + ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2
                  * ∫⁻ w', ∫⁻ y', ‖e w' y'‖ₑ
                      ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
                      ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
            * ‖B z.2.2‖ₑ
            * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ := by
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hker) le_rfl) le_rfl
      _ = _ := by ring
  exact hfac

end Work.BoseBoxFock
