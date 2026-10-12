import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairRung.integralAddLe
import Submission.Work.BoseFixB1B.pairRung.term2a
import Submission.Work.BoseFixB1B.pairRung.term2b
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.term2` — step 2 of the chain: the whole of Term 2

`Submission/Work/BoseFixB1S/chainIntegralQdep` gives

    boxA2 ≥ -S·X·(2π)⁻³∫ B q ²/(2𝒜 q)  -  (2π)⁻³∫ 𝒜 q · boxWinModePGen q ,

with `𝒜 q = [1/(n+1)]·[|q|-c]₊² + 2K_s(a v)/V`.  This module bounds the **whole** second term,

    (2π)⁻³ ∫ q, 𝒜 q · boxWinModePGen a volA Ac χ Ψ q
      ≤ tBwordKinInd a Ac volA χ c Ψ
        + 4 K_s κ² · (a v) · ((μ + N/V) · cnPlusBoxInd a Ac volA Ψ) ,

by splitting the (nonnegative) integrand into its two halves and adding the two bounds
`Work.BoseFixB1B.pairRung.term2a_le_word` (the `[|q|-c]₊²/(N+1)` half against the kinetic word)
and `Work.BoseFixB1B.pairRung.term2b_le_credit` (the `2K_s(a v)/V` half against the credit's
`(a v)(μ + N/V)·n₊` row).

**Why the split needs care.**  The two halves are individually nonnegative but need not be
integrable, and `MeasureTheory.integral_add` would then be unavailable (the Bochner integral of a
non-integrable nonnegative function is the junk value `0`, which would make the split *false*).
The correct tool is `Work.BoseFixB1B.pairRung.integral_add_le_of_nonneg`, which proves
`∫ (f+g) ≤ ∫ f + ∫ g` for `0 ≤ᵐ f`, `0 ≤ᵐ g` via the unconditional additivity of `∫⁻` and the
subadditivity of `ENNReal.toReal`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Nonnegativity of the windowed frame content** (both summands are `∫ (boxTauAnnGen ·)²`). -/
theorem boxWinModePGen_nonneg {N : ℕ} (a volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) (q : E3) :
    0 ≤ Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q := by
  rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen,
    Work.BoseFixB1.boxModePGen]
  exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => sq_nonneg _)

/-- **Term 2 of the chain.**  The whole frame term `(2π)⁻³∫ 𝒜·boxWinModePGen` is paid by the
kinetic word plus the credit's `(a v)(μ + N/V)·n₊` row. -/
theorem term2_le_word_add_credit {N : ℕ} {a volA V Ks κ μ av c : ℝ}
    {Ac : Set E3} {χ : E3 → ℝ} {Ψ : Submission.BoseGases.X N → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    (hc : 0 < c) {hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ}
    (hV : 0 < V) (hKs : 0 ≤ Ks) (hav : 0 ≤ av) (hμ : 0 ≤ μ)
    (hκ : ∀ z, |χ z| ≤ κ) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V)
          * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ Work.UBBInputs8.tBwordKinInd a Ac volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (N : ℝ) / V)
            * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
  set F : E3 → ℝ := fun q => (1 / ((N : ℝ) + 1)) * (Submission.BoseGases.fsKinCoeff c ‖q‖ *
      Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) with hFdef
  set G : E3 → ℝ := fun q => (2 * Ks * av / V) *
      Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q with hGdef
  -- the two halves are nonnegative
  have hF0 : 0 ≤ᵐ[(volume : Measure E3)] F := by
    refine Filter.Eventually.of_forall fun q => ?_
    rw [hFdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
        (boxWinModePGen_nonneg a volA Ac χ Ψ q))
  have hG0 : 0 ≤ᵐ[(volume : Measure E3)] G := by
    refine Filter.Eventually.of_forall fun q => ?_
    rw [hGdef]
    exact mul_nonneg (by positivity) (boxWinModePGen_nonneg a volA Ac χ Ψ q)
  -- and a.e. strongly measurable
  have hfk : Continuous (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖) := by
    rw [show (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖)
        = fun q : E3 => (max (‖q‖ - c) 0) ^ 2 from rfl]
    exact ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  have hP : AEStronglyMeasurable
      (fun q : E3 => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) (volume : Measure E3) :=
    aeStronglyMeasurable_boxWinModePGen hAcm hχc.continuous hΨc.continuous
  have hFm : AEStronglyMeasurable F (volume : Measure E3) := by
    rw [hFdef]
    exact (hfk.aestronglyMeasurable.mul hP).const_mul _
  have hGm : AEStronglyMeasurable G (volume : Measure E3) := by
    rw [hGdef]
    exact hP.const_mul _
  -- the integral split
  have hadd := integral_add_le_of_nonneg hF0 hG0 hFm hGm
  -- the two half-separated bounds
  have hHalf1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, F q) ≤
      Work.UBBInputs8.tBwordKinInd a Ac volA χ c Ψ := by
    have hInt : (∫ q : E3, F q)
        = (1 / ((N : ℝ) + 1)) * (∫ q : E3, Submission.BoseGases.fsKinCoeff c ‖q‖ *
            Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
      rw [hFdef]
      exact integral_const_mul _ _
    rw [hInt]
    have h2a := term2a_le_word (N := N) (a := a) (volA := volA) (c := c) (Ac := Ac) (χ := χ)
      (Ψ := Ψ) ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hχnn hc (hΨc := hΨc)
    have heq : ((2 * Real.pi) ^ 3)⁻¹ * ((1 / ((N : ℝ) + 1)) *
          (∫ q : E3, Submission.BoseGases.fsKinCoeff c ‖q‖ *
            Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q))
        = (1 / ((N : ℝ) + 1)) * (((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, Submission.BoseGases.fsKinCoeff c ‖q‖ *
            Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)) := by ring
    rw [heq]
    exact h2a
  have hHalf2 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, G q) ≤
      (4 * Ks * κ ^ 2) * av * ((μ + (N : ℝ) / V)
        * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ) := by
    have hInt : (∫ q : E3, G q) = (2 * Ks * av / V) *
        (∫ q : E3, Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
      rw [hGdef]
      exact integral_const_mul _ _
    rw [hInt]
    have h2b := term2b_le_credit (N := N) (a := a) (volA := volA) (V := V) (Ks := Ks) (κ := κ)
      (μ := μ) (av := av) (Ac := Ac) (χ := χ) (Ψ := Ψ) ha hAcm hAcsub hvol hvolpos
      hχc.continuous hχs hχsupp hκ (hΨ := hΨc.continuous) hV hKs hav hμ
    have heq : ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Ks * av / V) *
          (∫ q : E3, Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q))
        = (2 * Ks * av / V) * ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by ring
    rw [heq]
    exact h2b
  -- reassemble
  have hcongr : (∫ q : E3, (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / V) * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      = ∫ q : E3, (F q + G q) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    rw [hFdef, hGdef]
    ring
  rw [hcongr]
  have hmono : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, (F q + G q))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((∫ q : E3, F q) + ∫ q : E3, G q) :=
    mul_le_mul_of_nonneg_left hadd (by positivity)
  have hstep : ((2 * Real.pi) ^ 3)⁻¹ * ((∫ q : E3, F q) + ∫ q : E3, G q)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, F q) + ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, G q) := by
    ring
  rw [hstep] at hmono
  linarith [hmono, hHalf1, hHalf2]

end Work.BoseFixB1B.pairRung
