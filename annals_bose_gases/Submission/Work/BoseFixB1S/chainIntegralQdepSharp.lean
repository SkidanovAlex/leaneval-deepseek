import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chainIntegralQdepSharp {N : ℕ} {a volA S X : ℝ}
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ}
    {𝒲 B Acoef : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ∀ q : EuclideanSpace ℝ (Fin 3), 0 < Acoef q) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hpair : Work.BoseFixB1.boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      = (2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.pairW 𝒲 q * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q))
    (hB : ∀ q : EuclideanSpace ℝ (Fin 3), B q = Submission.BoseGases.pairW 𝒲 q / volA)
    (hBle : ∀ q : EuclideanSpace ℝ (Fin 3), |B q| ≤ Acoef q)
    (hmod : ∀ q : EuclideanSpace ℝ (Fin 3),
      -(((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2)
          * ((∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
              + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)) * S)
        ≤ Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
          + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
    (hXq : ∀ q : EuclideanSpace ℝ (Fin 3),
      (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
          + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2) ≤ X)
    (hintP : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q))
    (hintR : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q))
    (hIntQ : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2)) :
    Work.BoseFixB1.boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      ≥ -S * X * ((2 * Real.pi) ^ (-(3 : ℤ))
            * ∫ q : EuclideanSpace ℝ (Fin 3),
                (Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2)
        - ((2 * Real.pi) ^ (-(3 : ℤ))
            * ∫ q : EuclideanSpace ℝ (Fin 3),
                Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
  have hKc_nn : ∀ q : E3, 0 ≤ (Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2 := by
    intro q
    have hAq := hA q
    have hle : Real.sqrt (Acoef q ^ 2 - B q ^ 2) ≤ Acoef q := by
      have h1 : Acoef q ^ 2 - B q ^ 2 ≤ Acoef q ^ 2 := by nlinarith [sq_nonneg (B q)]
      calc Real.sqrt (Acoef q ^ 2 - B q ^ 2) ≤ Real.sqrt (Acoef q ^ 2) := Real.sqrt_le_sqrt h1
        _ = Acoef q := Real.sqrt_sq hAq.le
    linarith
  have hq : ∀ q : E3, -(((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) * (X * S))
      ≤ Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q := by
    intro q
    have hG2nn : 0 ≤ (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
        + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2) :=
      add_nonneg (integral_nonneg fun z => sq_nonneg _)
        (integral_nonneg fun z => sq_nonneg _)
    have hm := hmod q
    rw [mul_assoc] at hm
    have hGS : ((∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
        + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)) * S ≤ X * S :=
      mul_le_mul_of_nonneg_right (hXq q) hS
    have hK : ((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2)
          * (((∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
              + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2)) * S)
        ≤ ((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) * (X * S) :=
      mul_le_mul_of_nonneg_left hGS (hKc_nn q)
    linarith [hm, hK]
  have hcred_int : MeasureTheory.Integrable (fun q : E3 =>
      ((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) * (X * S)) :=
    hIntQ.mul_const (X * S)
  have hrhs_int : MeasureTheory.Integrable (fun q : E3 =>
      Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := hintP.add hintR
  have hmono : ∫ q : E3, -(((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) * (X * S))
      ≤ ∫ q : E3, (Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
          + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) :=
    integral_mono hcred_int.neg hrhs_int (fun q => hq q)
  have hcred_eq : ∫ q : E3, -(((Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) * (X * S))
      = -((X * S) * ∫ q : E3, (Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2) := by
    rw [integral_neg, integral_mul_const]
    ring
  have hrhs_eq : ∫ q : E3, (Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
      = (∫ q : E3, Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
        + ∫ q : E3, B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q :=
    integral_add hintP hintR
  have hBR_eq : ∫ q : E3, B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q
      = ∫ q : E3, Submission.BoseGases.pairW 𝒲 q
          * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    show B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q
      = Submission.BoseGases.pairW 𝒲 q
          * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
    rw [hB q, div_eq_mul_inv]
    ring
  have hlow : -((X * S) * ∫ q : E3, (Acoef q - Real.sqrt (Acoef q ^ 2 - B q ^ 2)) / 2)
        - (∫ q : E3, Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ ∫ q : E3, B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q := by
    have h := hmono
    rw [hcred_eq, hrhs_eq] at h
    linarith only [h]
  have hc0 : 0 ≤ (2 * Real.pi) ^ (-(3 : ℤ)) := by positivity
  rw [hpair, ← hBR_eq]
  have hfin := mul_le_mul_of_nonneg_left hlow hc0
  nlinarith [hfin, hc0]

end Work.BoseFixB1S
