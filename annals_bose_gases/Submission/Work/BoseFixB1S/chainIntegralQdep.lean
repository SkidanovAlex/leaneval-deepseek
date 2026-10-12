import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxTauGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chainIntegralQdep`

`chain_integral` (`Submission/Work/BoseFixB1S/chainCore.lean`) with a **`q`-dependent**
coefficient `𝒜 : E3 → ℝ` in place of the constant `Acoef` — the form the sharp row
(`FINDING_sharpA2Sliding.md` §5) needs.

The per-mode input is `hmod`, the window-mass bound is `hXq`, and the coefficient bound
`(A q - √(A q ² - B q ²))/2 ≤ B q ²/(2 A q)` is derived from `|B q| ≤ A q` and `A q > 0`
by pure arithmetic (`chainIntegralQdep_coeff_le`).  The `q`-integration is the same
`integral_mono`/`integral_add` bookkeeping as in `chainCore`; the integrability hypotheses
`hintP`, `hintR` and `hIntK` are exactly the ones needed.  Note that `hIntK` is *relative*
to `Acoef` (it bounds `q ↦ B q ²/A q`), which is what makes the `q`-dependent coefficient
harmless in the credit.

Everything in this file is proved (no `sorry`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The per-mode constant is at most `B²/(2A)`.**  For `A > 0` and `|B| ≤ A`,
`(A - √(A² - B²))/2 ≤ B²/(2A)`; this is the `hK` input at each `q`.  (Same arithmetic as
`Work.BoseFixB1S.bogoliubov_coeff_le`, restated here so the module is self-contained.) -/
theorem chainIntegralQdep_coeff_le {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ B ^ 2 / (2 * A) := by
  have h1 : 0 ≤ A ^ 2 - B ^ 2 := by
    have h := abs_le.mp hB
    nlinarith [h.1, h.2]
  set s := Real.sqrt (A ^ 2 - B ^ 2) with hs
  have hs2 : s ^ 2 = A ^ 2 - B ^ 2 := by rw [hs]; exact Real.sq_sqrt h1
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsA : s ≤ A := by
    have hsq : s ^ 2 ≤ A ^ 2 := by rw [hs2]; nlinarith [sq_nonneg B]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hs0, abs_of_pos hA] at h
  have hkey : (A - s) * A ≤ B ^ 2 := by nlinarith [hs2, hs0, hsA, hA]
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hgoal : (A - s) / 2 * (2 * A) ≤ B ^ 2 / (2 * A) * (2 * A) := by
    rw [div_mul_cancel₀ (B ^ 2) (ne_of_gt h2A)]
    calc (A - s) / 2 * (2 * A) = (A - s) * A := by ring
      _ ≤ B ^ 2 := hkey
  exact (mul_le_mul_iff_of_pos_right h2A).mp hgoal

/-- **The arithmetic core of the chain at a single `q`.**  From the per-mode Bogoliubov bound
(`hmod`), the coefficient bound `Kc ≤ B²/(2A)` (`hK`) and the window mass bound `G2 ≤ X`
(`hX`), one gets the constant-coefficient per-mode bound with credit `B²/(2A)·X·S`.
Pure arithmetic; no analysis. -/
theorem chainIntegralQdep_pointwise {A B Kc G2 X S P R : ℝ} (hA : 0 < A)
    (hK : Kc ≤ B ^ 2 / (2 * A)) (hX : G2 ≤ X) (hG2 : 0 ≤ G2) (hS : 0 ≤ S)
    (hmod : -(Kc * (G2 * S)) ≤ A * P + B * R) :
    -((B ^ 2 / (2 * A)) * (X * S)) ≤ A * P + B * R := by
  have hA2 : 0 < 2 * A := by linarith
  have hX0 : 0 ≤ X := le_trans hG2 hX
  have h1 : Kc * (G2 * S) ≤ (B ^ 2 / (2 * A)) * (X * S) := by
    have h2 : Kc * (G2 * S) ≤ (B ^ 2 / (2 * A)) * (G2 * S) := by
      refine mul_le_mul_of_nonneg_right hK ?_
      exact mul_nonneg hG2 hS
    have h3 : (B ^ 2 / (2 * A)) * (G2 * S) ≤ (B ^ 2 / (2 * A)) * (X * S) := by
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · nlinarith [hG2, hS, hX]
      · positivity
    linarith
  linarith

theorem chainIntegralQdep {N : ℕ} {a volA S X : ℝ} {Ac : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} {𝒲 B Acoef : EuclideanSpace ℝ (Fin 3) → ℝ}
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
    (hIntK : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => B q ^ 2 / Acoef q)) :
    Work.BoseFixB1.boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      ≥ -S * X * ((2 * Real.pi) ^ (-(3 : ℤ))
            * ∫ q : EuclideanSpace ℝ (Fin 3), B q ^ 2 / (2 * Acoef q))
        - ((2 * Real.pi) ^ (-(3 : ℤ))
            * ∫ q : EuclideanSpace ℝ (Fin 3), Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
  -- the per-mode bound, with the constant coefficient `B q ²/(2 A q)` at each `q`
  have hq : ∀ q : E3, -((B q ^ 2 / (2 * Acoef q)) * (X * S))
      ≤ Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q := by
    intro q
    have hG2nn : 0 ≤ (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
        + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2) :=
      add_nonneg (integral_nonneg fun z => sq_nonneg _)
        (integral_nonneg fun z => sq_nonneg _)
    have hm := hmod q
    rw [mul_assoc] at hm
    exact chainIntegralQdep_pointwise (hA q) (chainIntegralQdep_coeff_le (hA q) (hBle q))
      (hXq q) hG2nn hS hm
  -- integrability of the credit integrand, from `hIntK` (which is relative to `Acoef`)
  have hf_int : MeasureTheory.Integrable (fun q : E3 => B q ^ 2 / (2 * Acoef q)) := by
    refine (hIntK.div_const 2).congr ?_
    filter_upwards with q
    show B q ^ 2 / Acoef q / 2 = B q ^ 2 / (2 * Acoef q)
    rw [div_div, mul_comm (Acoef q) 2]
  have hcred_int : MeasureTheory.Integrable (fun q : E3 => (B q ^ 2 / (2 * Acoef q)) * (X * S)) :=
    hf_int.mul_const (X * S)
  have hPint : MeasureTheory.Integrable (fun q : E3 =>
      Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := hintP
  have hRint : MeasureTheory.Integrable (fun q : E3 =>
      B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := hintR
  have hrhs_int : MeasureTheory.Integrable (fun q : E3 =>
      Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := hPint.add hRint
  have hmono : ∫ q : E3, -((B q ^ 2 / (2 * Acoef q)) * (X * S))
      ≤ ∫ q : E3, (Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
          + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) :=
    integral_mono hcred_int.neg hrhs_int (fun q => hq q)
  have hcred_eq : ∫ q : E3, -((B q ^ 2 / (2 * Acoef q)) * (X * S))
      = -((X * S) * ∫ q : E3, B q ^ 2 / (2 * Acoef q)) := by
    rw [integral_neg, integral_mul_const]
    ring
  have hrhs_eq : ∫ q : E3, (Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
        + B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
      = (∫ q : E3, Acoef q * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
        + ∫ q : E3, B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q :=
    integral_add hPint hRint
  have hBR_eq : ∫ q : E3, B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q
      = ∫ q : E3, Submission.BoseGases.pairW 𝒲 q
          * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    show B q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q
      = Submission.BoseGases.pairW 𝒲 q
          * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
    rw [hB q, div_eq_mul_inv]
    ring
  have hlow : -((X * S) * ∫ q : E3, B q ^ 2 / (2 * Acoef q))
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
