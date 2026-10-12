import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.dict13Aux9
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux10` — the `RowData` of the `dict13_L1` instance

The data of the target `dict13_L1`: the state factor `Θ = boxRestrictC ℓ Ψ` (supported in the box
and bounded by the sup of `Ψ` on it), and the two weights `A = B = c · θ_Λ` (measurable, bounded by
`‖c‖`).  Everything is assembled into the `RowData` structure of `dict13Aux5`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox

set_option autoImplicit false

/-- The corpus' `θ_Λ = 1_{Λ(ℓ)}` is measurable. -/
theorem measurable_thetaFunCorpus (ℓ : ℝ) :
    Measurable (fun y : E3 => Work.BoseK15.corpusBox.thetaFun ℓ y) := by
  classical
  rw [show (fun y : E3 => Work.BoseK15.corpusBox.thetaFun ℓ y)
      = fun y : E3 => if y ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl]
  exact Measurable.ite (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
    measurable_const measurable_const

/-- `‖θ_Λ y‖ ≤ 1`. -/
theorem enorm_thetaFunCorpus_le_one (ℓ : ℝ) (y : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ ≤ 1 := by
  classical
  rw [show Work.BoseK15.corpusBox.thetaFun ℓ y
      = if y ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl]
  split_ifs
  · simp
  · simp

/-- The complex box restriction is the coercion of `block13_aux`'s real restriction. -/
theorem boxRestrictC_eq_ofRealR {n : ℕ} (ℓ : ℝ) (Φ : Xn n → ℝ) :
    boxRestrictC ℓ Φ = fun x => ((boxRestrR ℓ Φ x : ℝ) : ℂ) := by
  funext x
  simp only [boxRestrictC, boxRestrR, Complex.ofReal_mul]

/-- The support of `boxRestrictC ℓ Ψ` lies in the box. -/
theorem support_boxRestrictC {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) :
    Function.support (boxRestrictC ℓ Ψ) ⊆ abx n ℓ := by
  intro x hx
  refine boxRestrR_support ℓ Ψ ?_
  intro h0
  exact hx (by rw [boxRestrictC_eq_ofRealR]; simp only [h0, Complex.ofReal_zero])

/-- Measurability of the complex box restriction. -/
theorem measurable_boxRestrictC {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ) :
    Measurable (boxRestrictC ℓ Ψ) := by
  rw [boxRestrictC_eq_ofRealR]
  exact Complex.continuous_ofReal.measurable.comp (boxRestrR_measurable hΨc.measurable)

/-- **The `RowData` of the `dict13_L1` instance.** -/
noncomputable def rowDataBoxRestrict {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hℓ : 0 < ℓ) (hΨc : Continuous Ψ)
    {c : ℂ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    RowData n ℓ (boxRestrictC ℓ Ψ)
      (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
      (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) p := by
  have hC : ∀ x, |boxRestrR ℓ Ψ x| ≤ Classical.choose (boxRestrR_abs_le hℓ hΨc) :=
    Classical.choose_spec (boxRestrR_abs_le hℓ hΨc)
  have hCb : ∀ x,
      |boxRestrR ℓ Ψ x| ≤ max (Classical.choose (boxRestrR_abs_le hℓ hΨc)) 0 :=
    fun x => le_trans (hC x) (le_max_left _ _)
  exact
    { hℓ := hℓ
      hp := hp
      hΘs := support_boxRestrictC ℓ Ψ
      hΘm := measurable_boxRestrictC hΨc
      hAm := measurable_const.mul (measurable_thetaFunCorpus ℓ)
      hBm := measurable_const.mul (measurable_thetaFunCorpus ℓ)
      BΘ := ENNReal.ofReal (max (Classical.choose (boxRestrR_abs_le hℓ hΨc)) 0)
      hΘb := fun x => by
        rw [boxRestrictC_eq_ofRealR, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hCb x
      hΘf := ENNReal.ofReal_ne_top
      BA := ‖c‖ₑ
      hAb := fun y => by
        calc ‖c * Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ
            = ‖c‖ₑ * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ := enorm_mul c _
          _ ≤ ‖c‖ₑ * 1 := mul_le_mul' le_rfl (enorm_thetaFunCorpus_le_one ℓ y)
          _ = ‖c‖ₑ := mul_one _
      hAf := by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top
      BB := ‖c‖ₑ
      hBb := fun y => by
        calc ‖c * Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ
            = ‖c‖ₑ * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ := enorm_mul c _
          _ ≤ ‖c‖ₑ * 1 := mul_le_mul' le_rfl (enorm_thetaFunCorpus_le_one ℓ y)
          _ = ‖c‖ₑ := mul_one _
      hBf := by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top }

end Work.BoseBoxFock
