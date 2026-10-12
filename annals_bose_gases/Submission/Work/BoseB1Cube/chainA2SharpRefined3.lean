import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.slidingBogPortPrescribedEps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-- The `(2π)^{-3}`-normalisation in the two spellings of the workspace. -/
private lemma pi_zpow_neg_three_r :
    ((2 * Real.pi) ^ (-(3 : ℤ)) : ℝ) = ((2 * Real.pi) ^ 3)⁻¹ := by
  rw [zpow_neg]; rfl

theorem chainA2SharpRefined3 {N : ℕ} (hN : 1 ≤ N) {ℓ volA c Kc Ks av κ μ : ℝ}
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} {χ 𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ}
    (hℓ : 0 < ℓ) (hvolpos : 0 < volA) (hKs : 0 < Ks) (hav : 0 < av) (hc : 0 < c)
    (hKc : 0 ≤ Kc) (hKsKc : Kc ≤ 2 * Ks) (hμnn : 0 ≤ μ)
    (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube ℓ)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    (hχc2 : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, |χ z| ≤ κ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hnorm : (∫ x in Submission.BoseGases.abox (N + 1) ℓ, (Ψ x) ^ 2) = 1)
    (h𝒲int : MeasureTheory.Integrable 𝒲)
    (hsup : ∀ q : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.pairW 𝒲 q| ≤ Kc * av)
    (hfin : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
    (hintP : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA) *
        Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q))
    (hintR : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (1 / volA) * Submission.BoseGases.pairW 𝒲 q *
        Work.BoseFixB1.boxWinModeRGen ℓ volA Ac χ Ψ q))
    (hIntK : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2 /
        (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA)))
    (hIntQ : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA
        - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / volA) ^ 2
            - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2))
    (hI : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / volA) ^ 2
            - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2
      ≤ (1 + 8 * (av * c)) * (((N : ℝ) + 2) / (4 * volA ^ 2))
          * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
        + (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / volA ^ 2)
            * (1 + Real.log ((av * c)⁻¹))
        + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * volA))) :
    Work.BoseFixB1.boxA2 ℓ volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      ≥ - (Work.BoseFixB1S.boxFlatCount volA ℓ Ac Ψ) * (∫ z : EuclideanSpace ℝ (Fin 3), (χ z) ^ 2)
            * ( (1 + 8 * (av * c)) * (((N : ℝ) + 2) / (4 * volA ^ 2))
                  * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
                      (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
                + (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / volA ^ 2)
                    * (1 + Real.log ((av * c)⁻¹))
                + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * volA)) )
        - Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        - (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ) := by
  classical
  set 𝒜 : E3 → ℝ := fun q => 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
    + 2 * Ks * av / volA with h𝒜
  set ℬ : E3 → ℝ := fun q => Submission.BoseGases.pairW 𝒲 q / volA with hℬ
  set S : ℝ := Work.BoseFixB1S.boxFlatCount volA ℓ Ac Ψ with hS
  set X : ℝ := ∫ z : E3, (χ z) ^ 2 with hX
  have hApos : ∀ q : E3, 0 < 𝒜 q := by
    intro q
    rw [h𝒜]
    have h1 : 0 ≤ 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    have h2 : 0 < 2 * Ks * av / volA := by positivity
    linarith
  have hS0 : 0 ≤ S := by
    rw [hS, Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hX0 : 0 ≤ X := by
    rw [hX]; exact integral_nonneg (fun z => sq_nonneg _)
  have hpair : Work.BoseFixB1.boxA2 ℓ volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      = (2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q *
            (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen ℓ volA Ac χ Ψ q) := by
    have h := Work.BoseFixB1S.boxPairIntGenC2' (n := N + 1) (by omega) (a := ℓ) (volA := volA)
      hℓ hAcm hAcsub hvol hvolpos hχc2 hχs hχsupp h𝒲int hΨ
    rw [h, pi_zpow_neg_three_r]
  have hB : ∀ q : E3, ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := fun q => by rw [hℬ]
  have hBle : ∀ q : E3, |ℬ q| ≤ 𝒜 q := by
    intro q
    have h := Work.BoseFixB1B.pairRung.hBle_of (n := N + 1) (V := volA) (Ks := Ks) (av := av)
      (c := c) (K := Kc) (𝒲 := 𝒲) hvolpos hav.le hKsKc hsup q
    simp only [Nat.cast_add, Nat.cast_one] at h
    have h1 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    have h2 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    rw [h1, h2]
    exact h
  have hmod : ∀ q : E3,
      -(((𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
          * ((∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
              + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2))
          * (Work.BoseFixB1S.boxFlatCount volA ℓ Ac Ψ))
        ≤ 𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q
          + ℬ q * Work.BoseFixB1.boxWinModeRGen ℓ volA Ac χ Ψ q := by
    intro q
    have h := Work.BoseFixB1B.pairRung.modeBoundPointwise (n := N) (q := q) (a := ℓ)
      (Acoef := 𝒜 q) (B := ℬ q) (volA := volA) (κ := κ) (Ac := Ac) (χ := χ) (Ψ := Ψ)
      hℓ hAcm hAcsub hvol hvolpos hχc2.continuous hχs hχsupp hκ
      (le_trans (abs_nonneg (χ 0)) (hκ 0)) hΨ.continuous (hApos q) (hBle q)
    exact h
  have hXq : ∀ q : E3,
      (∫ z in Ac, (Work.BoseFixB1.boxWinModeReGen volA Ac χ q z) ^ 2)
          + (∫ z in Ac, (Work.BoseFixB1.boxWinModeImGen volA Ac χ q z) ^ 2) ≤ X := by
    intro q
    have h := Work.BoseFixB1S.winMode_mass_le (volA := volA) (Ac := Ac) hAcm hvol hvolpos
      hχc2.continuous hχs hχsupp q
    have hX1 : X = ∫ z : E3, (χ z) ^ 2 := by rw [hX]
    rw [hX1]
    exact h
  have hintP' : MeasureTheory.Integrable (fun q : E3 =>
      𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q) := by
    refine hintP.congr (Filter.Eventually.of_forall fun q => ?_)
    have h2 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    simp only []
    rw [h2]
  have hintR' : MeasureTheory.Integrable (fun q : E3 =>
      ℬ q * Work.BoseFixB1.boxWinModeRGen ℓ volA Ac χ Ψ q) := by
    refine hintR.congr (Filter.Eventually.of_forall fun q => ?_)
    have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    simp only []
    rw [h2]
    ring
  have hIntQ' : MeasureTheory.Integrable (fun q : E3 =>
      (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2) := by
    refine hIntQ.congr (Filter.Eventually.of_forall fun q => ?_)
    have hcast : ((N : ℝ) + 1 + 1) = ((N : ℝ) + 2) := by ring
    have h2 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    have h3 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    simp only []
    rw [h2, h3, hcast]
  -- ## the sharp chain
  have hchain := Work.BoseFixB1S.chainIntegralQdepSharp (N := N) (a := ℓ) (volA := volA)
    (S := S) (X := X) (Ac := Ac) (χ := χ) (Ψ := Ψ) (𝒲 := 𝒲) (B := ℬ) (Acoef := 𝒜)
    hApos hS0 hX0 hpair hB hBle hmod hXq hintP' hintR' hIntQ'
  -- ## the frame row, from `term2C2` at the chemical potential `μ`
  have hJ : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q)
      ≤ Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ) := by
    have h := Work.BoseFixB1B.pairRung.term2C2 (N := N + 1) (a := ℓ) (volA := volA) (V := volA)
      (Ks := Ks) (κ := κ) (μ := μ) (av := av) (c := c) (Ac := Ac) (χ := χ) (Ψ := Ψ)
      hℓ hAcm hAcsub hvol hvolpos hχc2 hχs hχsupp hχnn hc (hΨc := hΨ) hvolpos hKs.le hav.le
      hμnn hκ
    simp only [Nat.cast_add, Nat.cast_one] at h
    have hcongr : (∫ q : E3, 𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q)
        = ∫ q : E3, (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * av / volA) * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q := by
      have h2 : ∀ q : E3, 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * av / volA := fun q => by rw [h𝒜]
      simp only [h2]
    rw [hcongr, pi_zpow_neg_three_r]
    simpa only [mul_assoc] using h
  -- ## the sharp frequency integral, restated at `(𝒜, ℬ)`
  have hcast2 : ((N : ℝ) + 1 + 1) = ((N : ℝ) + 2) := by ring
  have hlam_eq : (∫ q : E3, (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
      = ∫ q : E3, (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * av / volA
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * av / volA) ^ 2
              - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    have h1 : 𝒜 q = 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜, hcast2]
    have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := hB q
    rw [h1, h2]
  -- ## the four-row right-hand side, as one atom `F`
  set F : ℝ := (1 + 8 * (av * c)) * (((N : ℝ) + 2) / (4 * volA ^ 2))
          * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
        + (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / volA ^ 2)
            * (1 + Real.log ((av * c)⁻¹))
        + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * volA)) with hFdef
  have hSX0 : 0 ≤ S * X := mul_nonneg hS0 hX0
  have hkey : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2) ≤ F := by
    rw [hFdef, hlam_eq, pi_zpow_neg_three_r]
    exact hI
  have hmul : S * X * ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2) ≤ S * X * F :=
    mul_le_mul_of_nonneg_left hkey hSX0
  have hneg : -(S * X * ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)) ≥ -(S * X * F) := by
    linarith only [hmul]
  have hJneg : -((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q)
      ≥ -(Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ)) := by
    linarith only [hJ]
  have hnorm : -(S * X * F) - (Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ))
      = -S * X * F - Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        - (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ) := by
    ring
  linarith only [hchain, hneg, hJneg, hnorm]

end Work.BoseB1Cube
