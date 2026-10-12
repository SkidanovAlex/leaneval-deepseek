import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13AesRowProd
import Submission.Work.BoseBoxFock.dict13Aux5
import Submission.Work.BoseBoxFock.dict13RowBoundMine
import Submission.Work.BoseBoxFock.dict13RowProdSubAe
import Submission.Work.BoseBoxFock.dict13RowShapeCongrAe
import Submission.Work.BoseBoxFock.dict13RowShapeEqProd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux6` — the `L¹` continuity and linearity of the block-I functional

With the domination bound `dict13LintegralRowProd`, the Fubini bridge `dict13RowShapeEqProd`, the
measurability `dict13AesRowProd` and the a.e. linearity `dict13RowProdSubAe`, the general block-I
functional `lhsGen` of `dict13Aux5` is shown to be

* integrable-valued (`rowProd_integrable`),
* `L¹`-Lipschitz in the pair kernel (`lhsGen_abs_le`), and
* linear in the pair kernel (`lhsGen_linear`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The `rowProd` integrand at the `Q M Q` kernel of `e` has finite integral whenever the kernel
has finite box `L¹` norm. -/
theorem rowProd_hasFiniteIntegral {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {p : Fin n × Fin n} (D : RowData n ℓ Θ A B p) {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e))
    (hfin : boxL1 ℓ e < ⊤) :
    HasFiniteIntegral (rowProd Θ A B (qmqKernel ℓ e) p)
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        ((volume : Measure E3).prod (volume : Measure E3))) := by
  obtain ⟨K, hK, hb⟩ := lintegral_rowProd_bound (n := n) (ℓ := ℓ) (Θ := Θ) (A := A) (B := B)
    (p := p) D.hℓ D.hp D.hΘs D.hΘb D.hAb D.hBb D.hΘf D.hAf D.hBf
  exact lt_of_le_of_lt (hb e hm)
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hfin)

/-- The `rowProd` integrand at the `Q M Q` kernel of a measurable kernel is integrable. -/
theorem rowProd_integrable {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {p : Fin n × Fin n} (D : RowData n ℓ Θ A B p) {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e)) (hfin : boxL1 ℓ e < ⊤) :
    Integrable (rowProd Θ A B (qmqKernel ℓ e) p)
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        ((volume : Measure E3).prod (volume : Measure E3))) :=
  ⟨dict13AesRowProd D.hΘm D.hAm D.hBm hm,
    rowProd_hasFiniteIntegral D hm hfin⟩

/-- **The `L¹` bound of the block-I functional.**  `|lhsGen| ≤ K · ∫∫_{Λ×Λ}‖e‖`. -/
theorem lhsGen_abs_le {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ} {p : Fin n × Fin n}
    (D : RowData n ℓ Θ A B p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ e : E3 → E3 → ℝ, Measurable (Function.uncurry e) →
      boxL1 ℓ e < ⊤ → |lhsGen ℓ Θ A B p e| ≤ K * (boxL1 ℓ e).toReal := by
  obtain ⟨K, hK, hb⟩ := lintegral_rowProd_bound (n := n) (ℓ := ℓ) (Θ := Θ) (A := A) (B := B)
    (p := p) D.hℓ D.hp D.hΘs D.hΘb D.hAb D.hBb D.hΘf D.hAf D.hBf
  refine ⟨(ℓ ^ 3)⁻¹ * K.toReal,
    mul_nonneg (inv_nonneg.mpr (pow_nonneg D.hℓ.le 3)) ENNReal.toReal_nonneg,
    fun e hm hfin => ?_⟩
  have hI : Integrable (rowProd Θ A B (qmqKernel ℓ e) p)
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        ((volume : Measure E3).prod (volume : Measure E3))) := rowProd_integrable D hm hfin
  have hbr : rowShape13 Θ A B (qmqKernel ℓ e) p
      = ∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
          ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
            ((volume : Measure E3).prod (volume : Measure E3))) :=
    dict13RowShapeEqProd D.hΘs hI
  have hbd : ‖∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          ((volume : Measure E3).prod (volume : Measure E3)))‖
      ≤ K.toReal * (boxL1 ℓ e).toReal := by
    have h2 : ‖∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          ((volume : Measure E3).prod (volume : Measure E3)))‖ₑ ≤ K * boxL1 ℓ e :=
      (enorm_integral_le_lintegral_enorm _).trans (hb e hm)
    have h3 : K * boxL1 ℓ e ≠ ⊤ := ENNReal.mul_ne_top hK (ne_of_lt hfin)
    calc ‖∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
            ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
              ((volume : Measure E3).prod (volume : Measure E3)))‖
        = (‖∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
            ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
              ((volume : Measure E3).prod (volume : Measure E3)))‖ₑ).toReal :=
          (toReal_enorm _).symm
      _ ≤ (K * boxL1 ℓ e).toReal := ENNReal.toReal_mono h3 h2
      _ = K.toReal * (boxL1 ℓ e).toReal := ENNReal.toReal_mul
  have hmain : |(rowShape13 Θ A B (qmqKernel ℓ e) p).re| ≤ K.toReal * (boxL1 ℓ e).toReal := by
    calc |(rowShape13 Θ A B (qmqKernel ℓ e) p).re|
        ≤ ‖rowShape13 Θ A B (qmqKernel ℓ e) p‖ := Complex.abs_re_le_norm _
      _ = ‖∫ z, rowProd Θ A B (qmqKernel ℓ e) p z
              ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
                ((volume : Measure E3).prod (volume : Measure E3)))‖ := by rw [hbr]
      _ ≤ K.toReal * (boxL1 ℓ e).toReal := hbd
  rw [lhsGen, abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg D.hℓ.le 3))]
  calc (ℓ ^ 3)⁻¹ * |(rowShape13 Θ A B (qmqKernel ℓ e) p).re|
      ≤ (ℓ ^ 3)⁻¹ * (K.toReal * (boxL1 ℓ e).toReal) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (pow_nonneg D.hℓ.le 3))
    _ = (ℓ ^ 3)⁻¹ * K.toReal * (boxL1 ℓ e).toReal := by ring

/-- **Linearity of the block-I functional in the pair kernel** (away from the linearity of the
Bochner integral, which needs the integrability hypotheses). -/
theorem lhsGen_linear {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ} {p : Fin n × Fin n}
    (D : RowData n ℓ Θ A B p) {e₁ e₂ : E3 → E3 → ℝ}
    (hm₁ : Measurable (Function.uncurry e₁)) (hm₂ : Measurable (Function.uncurry e₂))
    (him : Measurable (Function.uncurry (fun a b : E3 => e₁ a b - e₂ a b)))
    (hi₁ : boxL1 ℓ e₁ < ⊤) (hi₂ : boxL1 ℓ e₂ < ⊤)
    (hid : boxL1 ℓ (fun a b : E3 => e₁ a b - e₂ a b) < ⊤) :
    lhsGen ℓ Θ A B p e₁ - lhsGen ℓ Θ A B p e₂
      = lhsGen ℓ Θ A B p (fun a b : E3 => e₁ a b - e₂ a b) := by
  have hI₁ := rowProd_integrable D hm₁ hi₁
  have hI₂ := rowProd_integrable D hm₂ hi₂
  have hIid := rowProd_integrable D him hid
  have hae : (fun z : Xn n × (E3 × E3) => rowProd Θ A B (qmqKernel ℓ e₁) p z
        - rowProd Θ A B (qmqKernel ℓ e₂) p z)
      =ᵐ[(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        ((volume : Measure E3).prod (volume : Measure E3)))]
      (fun z : Xn n × (E3 × E3) =>
        rowProd Θ A B (qmqKernel ℓ (fun a b : E3 => e₁ a b - e₂ a b)) p z) :=
    dict13RowProdSubAe D.hℓ D.hp D.hΘs hm₁ hm₂ hi₁ hi₂
  have hcomplex : rowShape13 Θ A B (qmqKernel ℓ e₁) p - rowShape13 Θ A B (qmqKernel ℓ e₂) p
      = rowShape13 Θ A B (qmqKernel ℓ (fun a b : E3 => e₁ a b - e₂ a b)) p := by
    rw [dict13RowShapeEqProd D.hΘs hI₁, dict13RowShapeEqProd D.hΘs hI₂,
      dict13RowShapeEqProd D.hΘs hIid, ← MeasureTheory.integral_sub hI₁ hI₂]
    exact MeasureTheory.integral_congr_ae hae
  simp only [lhsGen]
  rw [← hcomplex, Complex.sub_re]
  ring

end Work.BoseBoxFock
