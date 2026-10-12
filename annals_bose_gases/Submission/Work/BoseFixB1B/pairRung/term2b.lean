import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairRung.framePGenNoClash
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.term2b` — step 2 of the chain: the `2K_s(a v)/V` half of Term 2

`Submission/Work/BoseFixB1S/chainIntegralQdep` bounds the pairing word by

    boxA2 ≥ -S·X·(2π)⁻³∫ B q ²/(2𝒜 q)  -  (2π)⁻³∫ 𝒜 q · boxWinModePGen q ,

where `𝒜 q = [1/(n+1)]·[|q|-c]₊² + 2K_s(a v)/V` and `B q = pairW 𝒲(q)/V`.  This module disposes
of the **second half** of the second term,

    (2K_s (a v)/V)·(2π)⁻³ ∫ q, boxWinModePGen a volA Ac χ Ψ q
      ≤ 4 K_s κ² · (a v) · ((μ + N/V) · cnPlusBoxInd a Ac volA Ψ) ,

against the credit's `C(a v)(μ + n/V)·boxQCount` row.  The only inputs are the frame bound
`Work.BoseFixB1B.pairRung.framePGenNoClash`

    (2π)⁻³ ∫ q, boxWinModePGen a volA Ac χ Ψ q ≤ 2κ² N · cnPlusBoxInd a Ac volA Ψ

and `0 ≤ μ` — note that **no** `μV ≥ 1` hypothesis is needed here: the frame bound produces the
*naked* slot count `N`, and `N/V ≤ μ + N/V` as soon as `μ ≥ 0`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Term 2b of the chain.**  The `2K_s(a v)/V` half of the frame term is paid by the credit's
`(a v)(μ + N/V)·n₊` row with the explicit constant `4 K_s κ²`. -/
theorem term2b_le_credit {N : ℕ} {a volA V Ks κ μ av : ℝ}
    {Ac : Set E3} {χ : E3 → ℝ} {Ψ : Submission.BoseGases.X N → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hκ : ∀ z, |χ z| ≤ κ) {hΨ : Continuous Ψ}
    (hV : 0 < V) (hKs : 0 ≤ Ks) (hav : 0 ≤ av) (hμ : 0 ≤ μ) :
    (2 * Ks * av / V) * ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (4 * Ks * κ ^ 2) * av * ((μ + (N : ℝ) / V)
          * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
  have hfr := framePGenNoClash (N := N) ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hκ hΨ
  have hQ0 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
    rw [Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hc0 : 0 ≤ (2 * Ks * av / V) := by positivity
  have hstep : (2 * Ks * av / V) * ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (2 * Ks * av / V) * (2 * κ ^ 2 * (N : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hfr hc0
  have hNV : (N : ℝ) / V ≤ μ + (N : ℝ) / V := by
    have h1 : 0 ≤ (N : ℝ) / V := div_nonneg (Nat.cast_nonneg N) hV.le
    linarith
  have hkey : (2 * Ks * av / V) * (2 * κ ^ 2 * (N : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ)
      ≤ (4 * Ks * κ ^ 2) * av * ((μ + (N : ℝ) / V)
          * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
    have hrw : (2 * Ks * av / V) * (2 * κ ^ 2 * (N : ℝ) * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ)
        = (4 * Ks * κ ^ 2) * av * ((N : ℝ) / V)
            * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by ring
    rw [hrw]
    have hfac : 0 ≤ (4 * Ks * κ ^ 2) * av := by positivity
    have hQ := hQ0
    nlinarith [mul_le_mul_of_nonneg_left hNV hfac, hQ,
      mul_nonneg hfac (div_nonneg (Nat.cast_nonneg N) hV.le)]
  linarith [hstep, hkey]

end Work.BoseFixB1B.pairRung
