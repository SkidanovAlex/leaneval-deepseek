import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1B.sharpTerm1Split
import Submission.Work.BoseFixB1B.slidingBogPortCube
import Submission.Work.BoseFixB1S.chainIntegralQdepSharp
import Submission.Work.BoseFixB1S.slidingNewtonMassSharpB1
import Submission.Work.BoseFixGlue.Pot.ellB_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.SmallBoxSliding Work.BoseBoxFix
  Work.BoseFixB1 Work.BoseFixB1S

theorem pi_zpow_neg_three_b : ((2 * Real.pi) ^ (-(3 : ℤ)) : ℝ) = ((2 * Real.pi) ^ 3)⁻¹ := by
  rw [zpow_neg]; rfl

/-- **The integrability of the exact Bogoliubov integrand**, from the crude `B²/𝒜` one.  Indeed
`0 ≤ (𝒜−√(𝒜²−ℬ²))/2 ≤ ℬ²/(2𝒜)` and `ℬ²/(2𝒜) = (ℬ²/𝒜)/2`; the exact integrand is a continuous
function of `(𝒜, ℬ²)`, and `ℬ² = 𝒜·(ℬ²/𝒜)` is a.e. strongly measurable because `ℬ²/𝒜` is
integrable and `𝒜` is continuous and positive. -/
theorem intQ_of_intK {N : ℕ} {V Ks av c : ℝ} {𝒲 : E3 → ℝ}
    (hV : 0 < V) (hKs : 0 < Ks) (hav : 0 < av)
    (hBle : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q / V|
      ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V)
    (hIntK : MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V))) :
    MeasureTheory.Integrable (fun q : E3 =>
      (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
        - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V) ^ 2
            - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2) := by
  set A : E3 → ℝ := fun q => 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
    + 2 * Ks * av / V with hA
  set B : E3 → ℝ := fun q => Submission.BoseGases.pairW 𝒲 q / V with hB
  have hApos : ∀ q : E3, 0 < A q := by
    intro q
    rw [hA]
    have h1 : 0 ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    have h2 : 0 < 2 * Ks * av / V := by positivity
    linarith
  have hAcont : Continuous A := by
    rw [hA]
    refine Continuous.add ?_ continuous_const
    refine Continuous.mul continuous_const ?_
    unfold Submission.BoseGases.fsKinCoeff
    fun_prop
  have hBle' : ∀ q : E3, |B q| ≤ A q := fun q => by rw [hA, hB]; exact hBle q
  have hdiv : MeasureTheory.Integrable (fun q : E3 => B q ^ 2 / A q) := by
    rw [hA, hB]; exact hIntK
  have hB2aesm : AEStronglyMeasurable (fun q : E3 => B q ^ 2) (volume : Measure E3) := by
    have h1 : AEStronglyMeasurable (fun q : E3 => B q ^ 2 / A q) (volume : Measure E3) :=
      hdiv.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : E3 => B q ^ 2 / A q * A q) (volume : Measure E3) :=
      h1.mul hAcont.aestronglyMeasurable
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    show B q ^ 2 / A q * A q = B q ^ 2
    rw [div_mul_cancel₀ _ (ne_of_gt (hApos q))]
  have hInt2 : MeasureTheory.Integrable (fun q : E3 => B q ^ 2 / (2 * A q)) := by
    refine (hdiv.div_const 2).congr (Filter.Eventually.of_forall fun q => ?_)
    show B q ^ 2 / A q / 2 = B q ^ 2 / (2 * A q)
    rw [div_div]; ring
  have hexpl : (fun q : E3 =>
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / V) ^ 2 - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2)
      = fun q : E3 => (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) / 2 := by
    funext q; rw [hA, hB]
  refine MeasureTheory.Integrable.mono' hInt2 ?_ ?_
  · rw [hexpl]
    have hsub : AEStronglyMeasurable (fun q : E3 => A q ^ 2 - B q ^ 2) (volume : Measure E3) :=
      (hAcont.measurable.pow_const 2).aestronglyMeasurable.sub hB2aesm
    have h1 : AEStronglyMeasurable (fun q : E3 => A q - Real.sqrt (A q ^ 2 - B q ^ 2))
        (volume : Measure E3) :=
      hAcont.aestronglyMeasurable.sub (Real.continuous_sqrt.comp_aestronglyMeasurable hsub)
    have h2 := h1.const_mul (1 / 2)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    ring
  · filter_upwards with q
    have hAq := hApos q
    have hAB : B q ^ 2 ≤ A q ^ 2 := by
      have h := abs_le.mp (hBle' q)
      nlinarith [h.1, h.2, le_of_lt hAq]
    have hnn : 0 ≤ A q ^ 2 - B q ^ 2 := by linarith [hAB]
    have hsq2 : Real.sqrt (A q ^ 2 - B q ^ 2) ^ 2 = A q ^ 2 - B q ^ 2 := Real.sq_sqrt hnn
    have hsq0 : 0 ≤ Real.sqrt (A q ^ 2 - B q ^ 2) := Real.sqrt_nonneg _
    have hsqle : Real.sqrt (A q ^ 2 - B q ^ 2) ≤ A q := by
      have h2 : Real.sqrt (A q ^ 2 - B q ^ 2) ^ 2 ≤ A q ^ 2 := by
        have hsub' : A q ^ 2 - B q ^ 2 ≤ A q ^ 2 := by linarith [sq_nonneg (B q)]
        exact hsq2.trans_le hsub'
      nlinarith [hsq0, hsq2, le_of_lt hAq]
    have hkey : (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) * (A q + Real.sqrt (A q ^ 2 - B q ^ 2))
        = B q ^ 2 := by nlinarith [hsq2]
    have h0 : 0 ≤ (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) / 2 := by linarith
    rw [Real.norm_of_nonneg h0]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hA0 : 0 ≤ A q := le_of_lt hAq
    have h1 : A q ≤ A q + Real.sqrt (A q ^ 2 - B q ^ 2) := by linarith
    have h2 : 0 ≤ A q - Real.sqrt (A q ^ 2 - B q ^ 2) := by linarith
    have h3 : (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) * A q ≤ B q ^ 2 := by
      have h4 : (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) * A q
          ≤ (A q - Real.sqrt (A q ^ 2 - B q ^ 2)) * (A q + Real.sqrt (A q ^ 2 - B q ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 h2
      linarith [h4, hkey]
    linarith [h3]


/-- **The sharp sliding Bogoliubov chain** (FS `lm:appbogolubov` with the prescribed-`ε` mass
row; the `K_s` of the half-axis no longer multiplies the sharp Newtonian row). -/
theorem chainA2SharpBeps {N : ℕ} (hN : 1 ≤ N) {ℓ volA c Kc Ks av κ μ δ : ℝ}
    {Ac : Set E3} {χ 𝒲 : E3 → ℝ} {Ψ : Submission.BoseGases.X (N + 1) → ℝ}
    (hℓ : 0 < ℓ) (hvolpos : 0 < volA) (hKs : 0 < Ks) (hav : 0 < av) (hc : 0 < c)
    (hKc : 0 ≤ Kc) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hKsKc : Kc ≤ 2 * Ks) (hμnn : 0 ≤ μ)
    (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube ℓ)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    (hχc2 : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, |χ z| ≤ κ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hnorm : (∫ x in Submission.BoseGases.abox (N + 1) ℓ, (Ψ x) ^ 2) = 1)
    (h𝒲int : MeasureTheory.Integrable 𝒲)
    (hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Kc * av)
    (hfin : MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
    (hintP : MeasureTheory.Integrable (fun q : E3 =>
      (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA) *
        Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q))
    (hintR : MeasureTheory.Integrable (fun q : E3 =>
      (1 / volA) * Submission.BoseGases.pairW 𝒲 q *
        Work.BoseFixB1.boxWinModeRGen ℓ volA Ac χ Ψ q))
    (hIntK : MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2 /
        (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA)))
    (hIntQ : MeasureTheory.Integrable (fun q : E3 =>
      (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA
        - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / volA) ^ 2
            - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2)) :
    Work.BoseFixB1.boxA2 ℓ volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      ≥ - (Work.BoseFixB1S.boxFlatCount volA ℓ Ac Ψ) * (∫ z : E3, (χ z) ^ 2)
            * ( (1 + Kc ^ 2 / (4 * Ks ^ 2)) *
                ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * volA * δ ^ 3)
                  + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * volA ^ 2) *
                      (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) ) )
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
    rw [h, pi_zpow_neg_three_b]
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
  have hIntK' : MeasureTheory.Integrable (fun q : E3 => ℬ q ^ 2 / 𝒜 q) := by
    refine hIntK.congr (Filter.Eventually.of_forall fun q => ?_)
    have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    have h3 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    simp only []
    rw [h2, h3]
  have hIntQ' : MeasureTheory.Integrable (fun q : E3 =>
      (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2) := by
    refine hIntQ.congr (Filter.Eventually.of_forall fun q => ?_)
    have hcast : ((N : ℝ) + 1 + 1) = ((N : ℝ) + 2) := by ring
    have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    have h3 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    simp only []
    rw [h2, h3, hcast]
  -- ## the chain
  have hchain := Work.BoseFixB1S.chainIntegralQdepSharp (N := N) (a := ℓ) (volA := volA) (S := S)
    (X := X) (Ac := Ac) (χ := χ) (Ψ := Ψ) (𝒲 := 𝒲) (B := ℬ) (Acoef := 𝒜)
    hApos hS0 hX0 hpair hB hBle hmod hXq hintP' hintR' hIntQ'
  -- ## the sharp first-term bound
  have hI : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3, (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
      ≤ (1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * volA * δ ^ 3)
            + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * volA ^ 2) *
                (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                  (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) ) := by
    have hcast : ((N : ℝ) + 1 + 1) = ((N : ℝ) + 2) := by ring
    have hIntQ'' : MeasureTheory.Integrable (fun q : E3 =>
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * av / volA) ^ 2
              - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2) := hIntQ
    have hbase := sharpTerm1Bound (N := N) (V := volA) (c := c) (Kc := Kc) (Ks := Ks)
      (av := av) (δ := δ) (g := fun q : E3 => Submission.BoseGases.pairW 𝒲 q)
      hvolpos hc hKs hav hKc hδ hδ1 hKsKc hsup hfin hIntQ''
    have hconv : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
          (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
            (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA
              - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                    + 2 * Ks * av / volA) ^ 2
                  - (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2)) / 2 := by
      rw [pi_zpow_neg_three_b]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
      have h3 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * av / volA := by rw [h𝒜]
      simp only []
      rw [h2, h3, hcast]
    rw [hconv]
    exact hbase
  -- ## the spectral word and the credit
  have hJ : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q)
      ≤ Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ) := by
    have h := Work.BoseFixB1B.pairRung.term2C2 (N := N + 1) (a := ℓ) (volA := volA) (V := volA)
      (Ks := Ks) (κ := κ) (μ := μ) (av := av) (c := c) (Ac := Ac) (χ := χ) (Ψ := Ψ)
      (hΨc := hΨ)
      hℓ hAcm hAcsub hvol hvolpos hχc2 hχs hχsupp hχnn hc hvolpos hKs.le hav.le hμnn hκ
    simp only [Nat.cast_add, Nat.cast_one] at h
    have hL : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
          𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q)
        = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
            (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA)
              * Work.BoseFixB1.boxWinModePGen ℓ volA Ac χ Ψ q) := by
      rw [pi_zpow_neg_three_b]
    rw [hL]
    exact h
  -- ## combine
  have hSX : 0 ≤ S * X := mul_nonneg hS0 hX0
  have hI2 : S * X * ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        (𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
      ≤ S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * volA * δ ^ 3)
            + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * volA ^ 2) *
                (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                  (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) )) :=
    mul_le_mul_of_nonneg_left hI hSX
  have hgoal : - S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * volA * δ ^ 3)
            + (1 + 8 * δ) * ((N : ℝ) + 2) / (4 * volA ^ 2) *
                (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                  (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) ))
      - Work.UBBInputs8.tBwordKinInd ℓ Ac volA χ c Ψ
      - (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
          * Work.UBBInputs8.cnPlusBoxInd ℓ Ac volA Ψ)
      ≤ Work.BoseFixB1.boxA2 ℓ volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ := by
    have h1 := hchain
    have h2 := hJ
    linarith [h1, h2]
  rw [hS, hX] at hgoal
  exact hgoal


/-- **The low-band / credit arithmetic (cleared form).** -/
private lemma bandCreditCore {Bc c0 V n C av mu θ : ℝ} (hV : 0 < V) (hc0 : 0 < c0)
    (hθ : 0 < θ) (hn : 0 ≤ n) (hBc : 0 ≤ Bc) (hcase : θ * c0 * (n + 1) / 2 < Bc)
    (hcred : 2 * Bc ^ 2 * V / (θ * c0) ≤ C * av * mu * V ^ 2) :
    n * Bc * V ≤ C * av * mu * V ^ 2 := by
  have hpos : 0 < Bc := lt_of_le_of_lt (by positivity) hcase
  have h1 : n + 1 < 2 * Bc / (θ * c0) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith [hcase]
  have hnc : (n + 1) * (θ * c0) < 2 * Bc := (lt_div_iff₀ (by positivity)).mp h1
  have h2 : n * Bc * V < 2 * Bc ^ 2 * V / (θ * c0) := by
    rw [lt_div_iff₀ (by positivity)]
    have h3 : n * (θ * c0) * (Bc * V) < (2 * Bc) * (Bc * V) := by
      refine mul_lt_mul_of_pos_right ?_ (mul_pos hpos hV)
      nlinarith [hnc, hn]
    nlinarith [h3]
  linarith [h2, hcred]

/-- **The prescribed-`eps` row arithmetic of the sliding Bogoliubov port.** -/
theorem epsRowArithBeps {n V av c Kc Ks δ K1 D c0 S X mu C J0 θ : ℝ}
    (hV : 0 < V) (hav : 0 < av) (hc : 0 < c) (hKs : 0 < Ks) (hKc : 0 ≤ Kc)
    (hδ : 0 < δ) (hD : 0 < D) (hK1 : 0 ≤ K1) (hc0 : 0 < c0) (hmu : 0 < mu)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hτ1 : Kc ^ 2 / (4 * Ks ^ 2) ≤ 1)
    (hn0 : 0 ≤ n) (hS0 : 0 ≤ S) (hSle : S ≤ n) (hX0 : 0 ≤ X) (hXle : X ≤ V)
    (hJ0 : 0 ≤ J0) (hJ : J0 ≤ K1 * D) (hC0 : 0 ≤ C) (hc6 : c ^ 6 * V ≤ mu)
    (hmain : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * K1 ≤ 2 * (1 - θ) * c0 / D)
    (hcred : 8 * (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)) ≤ C) :
    (1 / 2) * c0 * (((n + 1) * n) / V ^ 2) * X + C * av * mu
      ≥ S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) *
          ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
            + (1 + 8 * δ) * (n + 1) / (4 * V ^ 2) * J0)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hV2 : 0 < V ^ 2 := by positivity
  have h1τ : 0 < 1 + Kc ^ 2 / (4 * Ks ^ 2) := by positivity
  have hτ0 : 0 ≤ Kc ^ 2 / (4 * Ks ^ 2) := by positivity
  have hτ4 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) ^ 2 ≤ 4 := by nlinarith [hτ0, hτ1]
  have h1δ : 0 ≤ 1 + 8 * δ := by linarith
  have hn1 : 0 ≤ n + 1 := by linarith
  have hKD : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * K1 * D ≤ 2 * (1 - θ) * c0 := by
    have h := (le_div_iff₀ hD).mp hmain
    linarith [h]
  -- (i) the sharp Newtonian row (cleared of the `V`-denominators)
  have hsharp : S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * J0)
      ≤ (1 - θ) * ((1 / 2) * c0 * (n + 1) * n * X) := by
    have hcoef : 0 ≤ (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 := by positivity
    have hcc : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * (K1 * D)
        ≤ (1 - θ) * c0 * ((n + 1) / 2) := by
      have h1 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * (K1 * D)
          = ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * K1 * D) * ((n + 1) / 4) := by ring
      have h2 : ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * K1 * D) * ((n + 1) / 4)
          ≤ (2 * (1 - θ) * c0) * ((n + 1) / 4) :=
        mul_le_mul_of_nonneg_right hKD (by linarith [hn1])
      have h3 : (2 * (1 - θ) * c0) * ((n + 1) / 4) = (1 - θ) * c0 * ((n + 1) / 2) := by ring
      linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
    have h3 : 0 ≤ (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * J0 :=
      mul_nonneg hcoef hJ0
    calc S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * J0)
        ≤ n * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * J0) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hX0) h3
      _ ≤ n * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * (K1 * D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ hcoef)
            (mul_nonneg hn0 hX0)
      _ ≤ n * X * ((1 - θ) * c0 * ((n + 1) / 2)) :=
          mul_le_mul_of_nonneg_left hcc (mul_nonneg hn0 hX0)
      _ = (1 - θ) * ((1 / 2) * c0 * (n + 1) * n * X) := by ring
  -- (ii) the low-momentum band, now carrying the whole `(1+τ²)` factor
  set Bc : ℝ := (1 + Kc ^ 2 / (4 * Ks ^ 2))
    * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) with hBcdef
  have hBc0 : 0 ≤ Bc := by rw [hBcdef]; positivity
  have hbandpay : S * X * Bc
      ≤ θ * ((1 / 2) * c0 * (n + 1) * n * X) + C * av * mu * V ^ 2 := by
    by_cases hb : Bc ≤ θ * c0 * (n + 1) / 2
    · have h3 : S * X * Bc ≤ n * X * (θ * c0 * (n + 1) / 2) := by
        calc S * X * Bc ≤ n * X * Bc :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hX0) hBc0
          _ ≤ n * X * (θ * c0 * (n + 1) / 2) :=
              mul_le_mul_of_nonneg_left hb (mul_nonneg hn0 hX0)
      have heq : n * X * (θ * c0 * (n + 1) / 2) = θ * ((1 / 2) * c0 * (n + 1) * n * X) := by ring
      have hnn : 0 ≤ C * av * mu * V ^ 2 := by positivity
      linarith [h3, heq.le, heq.ge, hnn]
    · have hlt : θ * c0 * (n + 1) / 2 < Bc := lt_of_not_ge hb
      have hbase : 2 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2 * V
            / (θ * c0)
          = (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ) / 2)
            * (av * (c ^ 6 * V) * V ^ 2) := by
        field_simp <;> ring
      have hstep1 : (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ) / 2)
            * (av * (c ^ 6 * V) * V ^ 2)
          ≤ (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)) * (av * mu * V ^ 2) := by
        have h1 : (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ) / 2)
              * (av * (c ^ 6 * V) * V ^ 2)
            ≤ (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ) / 2)
              * (av * mu * V ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc6 hav.le) (by positivity))
            (by positivity)
        have h2 : 0 ≤ (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
            * (av * mu * V ^ 2) := by positivity
        nlinarith [h1, h2]
      have hsq : (1 + Kc ^ 2 / (4 * Ks ^ 2)) ^ 2
            * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2
          ≤ 4 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2 :=
        mul_le_mul_of_nonneg_right hτ4 (by positivity)
      have hBcsq : Bc ^ 2 = (1 + Kc ^ 2 / (4 * Ks ^ 2)) ^ 2
          * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2 := by
        rw [hBcdef]; ring
      have hstep2 : 2 * Bc ^ 2 * V / (θ * c0)
          ≤ 4 * (2 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2
              * V / (θ * c0)) := by
        rw [hBcsq]
        calc 2 * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) ^ 2
              * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2) * V / (θ * c0)
            = (2 * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) ^ 2
                * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2))
              * (V / (θ * c0)) := by ring
          _ ≤ (2 * (4 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2))
              * (V / (θ * c0)) :=
              mul_le_mul_of_nonneg_right (by linarith [hsq]) (by positivity)
          _ = 4 * (2 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2
              * V / (θ * c0)) := by ring
      have hstep3 : 4 * (2 * (Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)) ^ 2
            * V / (θ * c0))
          ≤ 4 * ((Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
              * (av * mu * V ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_trans (le_of_eq hbase) hstep1) (by norm_num)
      have hstep4 : 4 * ((Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
            * (av * mu * V ^ 2))
          ≤ C * av * mu * V ^ 2 := by
        have hY : 0 ≤ av * mu * V ^ 2 := by positivity
        have h1 := mul_le_mul_of_nonneg_right hcred hY
        have h2 : 4 * ((Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
            * (av * mu * V ^ 2))
            ≤ 8 * (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
              * (av * mu * V ^ 2) := by
          have h3 : 0 ≤ (Kc ^ 4 * av / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ))
              * (av * mu * V ^ 2) := by positivity
          linarith [h3]
        have h1b : C * (av * mu * V ^ 2) = C * av * mu * V ^ 2 := by ring
        rw [← h1b]
        exact le_trans h2 h1
      have hcredge : 2 * Bc ^ 2 * V / (θ * c0) ≤ C * av * mu * V ^ 2 :=
        le_trans hstep2 (le_trans hstep3 hstep4)
      have hload : S * X * Bc ≤ n * Bc * V := by
        have hSX : S * X ≤ n * V := by
          calc S * X ≤ n * X := mul_le_mul_of_nonneg_right hSle hX0
            _ ≤ n * V := mul_le_mul_of_nonneg_left hXle hn0
        calc S * X * Bc ≤ n * V * Bc := mul_le_mul_of_nonneg_right hSX hBc0
          _ = n * Bc * V := by ring
      have hcore := bandCreditCore hV hc0 hθ hn0 hBc0 hlt hcredge
      have hnn4 : 0 ≤ θ * ((1 / 2) * c0 * (n + 1) * n * X) := by positivity
      linarith [hload, hcore, hnn4]
  -- assemble in the cleared form
  have hcl2 : S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
        * ( Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)
          + (1 + 8 * δ) * (n + 1) / 4 * J0))
      ≤ (1 / 2) * c0 * (n + 1) * n * X + C * av * mu * V ^ 2 := by
    have hdecomp : S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
          * ( Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)
            + (1 + 8 * δ) * (n + 1) / 4 * J0))
        = S * X * Bc
          + S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) * (n + 1) / 4 * J0) := by
      rw [hBcdef]; ring
    have hhalf : (1 / 2) * c0 * (n + 1) * n * X
        = (1 - θ) * ((1 / 2) * c0 * (n + 1) * n * X)
          + θ * ((1 / 2) * c0 * (n + 1) * n * X) := by ring
    rw [hdecomp, hhalf]
    linarith [hsharp, hbandpay]
  -- undo the clearing of `V`
  have e1 : S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
        * ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
          + (1 + 8 * δ) * (n + 1) / (4 * V ^ 2) * J0)) * V ^ 2
      = S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
          * ( Kc ^ 2 * av * c ^ 3 * V / (48 * Real.pi ^ 2 * Ks * δ ^ 3)
            + (1 + 8 * δ) * (n + 1) / 4 * J0)) := by
    field_simp <;> ring
  have e2 : ((1 / 2) * c0 * (((n + 1) * n) / V ^ 2) * X + C * av * mu) * V ^ 2
      = (1 / 2) * c0 * (n + 1) * n * X + C * av * mu * V ^ 2 := by
    field_simp <;> ring
  have hstep : S * X * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
        * ( Kc ^ 2 * av * c ^ 3 / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
          + (1 + 8 * δ) * (n + 1) / (4 * V ^ 2) * J0)) * V ^ 2
      ≤ ((1 / 2) * c0 * (((n + 1) * n) / V ^ 2) * X + C * av * mu) * V ^ 2 := by
    rw [e1, e2]
    exact hcl2
  exact (mul_le_mul_iff_of_pos_right hV2).mp hstep


/-- **The two-factor smallness at the sliding box.**  For every `eps > 0` and every fixed
`K ≥ 0` there is `ε₀ > 0` such that at every admissible diluteness
`K·[(R/ℓ)² + (R/(ℓd))²] ≤ eps`, where `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`. -/
theorem exists_eps_twoFactorSmall {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {eps K : ℝ} (heps : 0 < eps) (hK : 0 ≤ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      K * ((R / Work.BoseFixB1.bSide v μ) ^ 2
        + (R / (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)) ^ 2) ≤ eps := by
  set a : ℝ := _root_.BoseGases.a v with hadef
  set M : ℝ := 2 * K * (R / a) ^ 2 + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMge : 2 * K * (R / a) ^ 2 ≤ M := by rw [hMdef]; linarith
  refine ⟨min 1 ((eps / M) ^ (323 / 314 : ℝ)), lt_min one_pos
    (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro μ hAdm
  obtain ⟨hμpos, hμa, -⟩ := hAdm
  set t : ℝ := μ * a ^ 3 with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := le_trans hμa (min_le_left _ _)
  have htε : t ≤ (eps / M) ^ (323 / 314 : ℝ) := le_trans hμa (min_le_right _ _)
  have hXp1 : Work.BoseBox.fsXp t 1 ≤ 1 := Work.BoseBox.fsXp_le_one htpos ht1 (by norm_num)
  have hXp0 : 0 < Work.BoseBox.fsXp t 1 := Work.BoseBox.fsXp_pos htpos
  -- the explicit forms of `ℓ` and `ℓ d`
  have hside := Work.BoseFixB1.sideAt_eq_fsXp (A := a) (μ := μ) hav hμpos
  have hdl := Work.BoseFixB1.d_mul_sideAt_eq (A := a) (μ := μ) hav hμpos
  have hbside : Work.BoseFixB1.bSide v μ = a * Work.BoseBox.fsXp t (-163) := by
    rw [Work.BoseFixB1.bSide, hside, ← htdef]
  have hbdl : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
      = a * Work.BoseBox.fsXp t (-157) := by
    rw [Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm, hdl, ← htdef]
  -- `R/ℓ = (R/a)·Xp^{163}`, `R/(ℓd) = (R/a)·Xp^{157}`
  have hXpi : (Work.BoseBox.fsXp t (-163))⁻¹ = Work.BoseBox.fsXp t 163 := by
    rw [Work.BoseBox.fsXp_inv htpos]
    congr 1; ring
  have hXpi2 : (Work.BoseBox.fsXp t (-157))⁻¹ = Work.BoseBox.fsXp t 157 := by
    rw [Work.BoseBox.fsXp_inv htpos]
    congr 1; ring
  have hane : a ≠ 0 := ne_of_gt hav
  have hXpne : Work.BoseBox.fsXp t (-163) ≠ 0 := ne_of_gt (Work.BoseBox.fsXp_pos htpos)
  have hXpne2 : Work.BoseBox.fsXp t (-157) ≠ 0 := ne_of_gt (Work.BoseBox.fsXp_pos htpos)
  have e1 : R / Work.BoseFixB1.bSide v μ = (R / a) * Work.BoseBox.fsXp t 163 := by
    rw [hbside, div_mul_eq_div_div, div_eq_mul_inv, hXpi]
  have e2 : R / (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
      = (R / a) * Work.BoseBox.fsXp t 157 := by
    rw [hbdl, div_mul_eq_div_div, div_eq_mul_inv, hXpi2]
  -- powers of `Xp`
  have hp163 : (Work.BoseBox.fsXp t 1) ^ 163 = Work.BoseBox.fsXp t 163 := by
    rw [Work.BoseBox.fsXp_pow htpos.le 1 163]; norm_num
  have hp157 : (Work.BoseBox.fsXp t 1) ^ 157 = Work.BoseBox.fsXp t 157 := by
    rw [Work.BoseBox.fsXp_pow htpos.le 1 157]; norm_num
  have hp326 : Work.BoseBox.fsXp t 326 ≤ Work.BoseBox.fsXp t 314 :=
    Work.BoseBox.fsXp_le_fsXp htpos ht1 (by norm_num)
  have hsq : (Work.BoseBox.fsXp t 163) ^ 2 + (Work.BoseBox.fsXp t 157) ^ 2
      ≤ 2 * Work.BoseBox.fsXp t 314 := by
    have h1 : (Work.BoseBox.fsXp t 163) ^ 2 = Work.BoseBox.fsXp t 326 := by
      rw [← hp163, ← pow_mul]
      rw [Work.BoseBox.fsXp_pow htpos.le 1 326]; norm_num
    have h2 : (Work.BoseBox.fsXp t 157) ^ 2 = Work.BoseBox.fsXp t 314 := by
      rw [← hp157, ← pow_mul]
      rw [Work.BoseBox.fsXp_pow htpos.le 1 314]; norm_num
    rw [h1, h2]
    linarith [hp326]
  -- `Xp^{314} ≤ eps/M`
  have h314 : Work.BoseBox.fsXp t 314 ≤ eps / M := by
    have h1 : Work.BoseBox.fsXp t 314 = t ^ ((314 : ℝ) / 323) := rfl
    rw [h1]
    have h2 : t ^ ((314 : ℝ) / 323) ≤ ((eps / M) ^ (323 / 314 : ℝ)) ^ ((314 : ℝ) / 323) :=
      Real.rpow_le_rpow htpos.le htε (by norm_num)
    have h3 : ((eps / M) ^ (323 / 314 : ℝ)) ^ ((314 : ℝ) / 323) = eps / M := by
      rw [← Real.rpow_mul (le_of_lt (by positivity : (0:ℝ) < eps / M))]
      norm_num
    rw [h3] at h2
    exact h2
  have hgoal : (Work.BoseBox.fsXp t 163) ^ 2 + (Work.BoseBox.fsXp t 157) ^ 2
      ≤ (eps / M) * 2 / 1 := by linarith [hsq, h314]
  rw [e1, e2]
  have hRa : 0 ≤ (R / a) ^ 2 := sq_nonneg _
  calc K * (((R / a) * Work.BoseBox.fsXp t 163) ^ 2
        + ((R / a) * Work.BoseBox.fsXp t 157) ^ 2)
      = K * (R / a) ^ 2 * ((Work.BoseBox.fsXp t 163) ^ 2 + (Work.BoseBox.fsXp t 157) ^ 2) := by ring
    _ ≤ K * (R / a) ^ 2 * (2 * (eps / M)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK hRa)
        linarith [hgoal]
    _ ≤ eps := by
        have h1 : K * (R / a) ^ 2 * (2 * (eps / M)) = (2 * K * (R / a) ^ 2) * (eps / M) := by ring
        rw [h1]
        have h2 : (2 * K * (R / a) ^ 2) * (eps / M) ≤ M * (eps / M) :=
          mul_le_mul_of_nonneg_right hMge (by positivity)
        have h3 : M * (eps / M) = eps := by field_simp
        linarith [h2, h3.le, h3.ge]

/-- **FS `lm:appbogolubov`, `eq:simpleaprioribog` (`final_v2.tex` l.3776), in the matched-window
vocabulary**: the proved `Work.BoseFixB1B.SlidingBogPortB` (`chiCubeSlots.lean:93`, proved as
`slidingBogPortCube`) with its mass-row constant **prescribed**: for every `eps > 0` (the
`eps` precedes the `∃ ε₀ C`, so `C = C_eps` may depend on it), the mass row carries
`(1 + eps) * g0w0Mass h + eps * (a v)` — note the `eps * (a v)` **inside** the row, which is FS's
form and is what `lm:w2>w1`'s `eq:wepsilong` converts wholesale into `(3/4)∬w_{1,B} + ...`.

Why it is not the proved port: `Work.BoseFixB1B.slidingChainArithB` carries `hηK : 8K ≤ 1+η`
and uses it to make the mass row dominate an interior loss that scales like `n²`, while the credit
rows are only `O(n)`; the proved port therefore instantiates `η = 8 K_s + 1 ≥ 9`.  FS get the
prescribed `eps` at l.3823 by taking `K_s` large and `eps`-dependent and splitting the
`|p|`-integral at `|p| = 2 (dsℓ)^{-1}` (main term against the sharp `∫Ŵ₁²/p²`, the complementary
piece paid in `C_eps`).  Expect a re-derivation of the Bogoliubov step with `K_s ≥ 8 C_eps`, not a
constant swap. -/
theorem slidingBogPortPrescribedEps {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {eps : ℝ} (heps : 0 < eps) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          -((1 / 2) * ((1 + eps) * Submission.BoseGases.g0w0Mass h + eps * (_root_.BoseGases.a v))
                * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u
              + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                  * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
              + C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ))
            ≤ Work.BoseFixB1B.bSpectralCubeB v μ (Φ : Submission.BoseGases.X n → ℝ) u
              + Work.BoseFixB1B.bA2B h μ (Φ : Submission.BoseGases.X n → ℝ) u := by 
  classical
  obtain ⟨Kc, hKc0, hKcbound⟩ :=
    Work.BoseFixB1S.nuPairWNuIntegrable (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨K1s, hK1s0, hK1sh⟩ :=
    Work.BoseFixB1S.slidingNewtonMassSharpB1 (v := v) (R := R) hv_supp hR hv hvrad hv1 h
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε₁, hε₁pos, hreg⟩ :=
    Work.BoseFixB1S.admGoodSetRegime2 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := Work.BoseFixGlue.Pot.ellB_ge (v := v) hav hR
  obtain ⟨ε₂, hε₂pos, hsmall⟩ :=
    exists_eps_twoFactorSmall (v := v) h hv hvrad hR hv_supp hav (eps := min eps 1 / 32) (K := K1s)
      (by positivity) hK1s0
  set D : ℝ := Submission.BoseGases.g0w0Mass (v := v) h with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, ← Work.BoseFixB1B.PairMass_eq_g0w0Mass]
    exact Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav
  set δ : ℝ := min (1 / 2) (min eps 1 / 256) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδle : δ ≤ 1 / 2 := min_le_left _ _
  have hδsmall : 8 * δ ≤ min eps 1 / 32 := by
    have h : δ ≤ min eps 1 / 256 := min_le_right _ _
    linarith
  set θ : ℝ := min (1 / 4) (eps / (8 * (1 + eps))) with hθdef
  have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθle : θ ≤ 1 / 2 := le_trans (min_le_left _ _) (by norm_num)
  have hθsmall : 1 + 3 * eps / 4 ≤ (1 - θ) * (1 + eps) := by
    have h1 : θ ≤ eps / (8 * (1 + eps)) := min_le_right _ _
    have h2 : (0:ℝ) < 1 + eps := by linarith
    have h3 : θ * (1 + eps) ≤ eps / 8 := by
      have h4 : (eps / (8 * (1 + eps))) * (1 + eps) = eps / 8 := by field_simp
      rw [← h4]
      exact mul_le_mul_of_nonneg_right h1 h2.le
    nlinarith [h3]
  set Ks : ℝ := max 1 (max (Kc / 2) (4 * Kc / min eps 1)) with hKsdef
  have hKs0 : 0 < Ks := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKsKc : Kc ≤ 2 * Ks := by
    have h1 : Kc / 2 ≤ Ks := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hτ2 : Kc ^ 2 / (4 * Ks ^ 2) ≤ min eps 1 / 32 := by
    by_cases hKcz : Kc = 0
    · rw [hKcz, zero_pow (by norm_num : 2 ≠ 0), zero_div]
      exact div_nonneg (le_of_lt (lt_min heps one_pos)) (by norm_num)
    have hKcpos : 0 < Kc := lt_of_le_of_ne hKc0 (Ne.symm hKcz)
    have hKsge : 4 * Kc / min eps 1 ≤ Ks := le_trans (le_max_right _ _) (le_max_right _ _)
    have hminpos : 0 < min eps 1 := lt_min heps one_pos
    have h1 : Kc / (2 * Ks) ≤ min eps 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ hminpos] at hKsge
      nlinarith [hKsge]
    have h2 : 0 ≤ Kc / (2 * Ks) := by positivity
    have h3 : (Kc / (2 * Ks)) ^ 2 ≤ (min eps 1 / 8) ^ 2 := by
      exact pow_le_pow_left₀ h2 h1 2
    have h4 : (min eps 1 / 8) ^ 2 ≤ min eps 1 / 32 := by
      have h5 : min eps 1 ≤ 1 := min_le_right _ _
      have h7 : 0 < min eps 1 := hminpos
      nlinarith [h5, h7]
    have h8 : Kc ^ 2 / (4 * Ks ^ 2) = (Kc / (2 * Ks)) ^ 2 := by field_simp; ring
    rw [h8]
    linarith [h3, h4]
  set c0 : ℝ := (1 + eps) * D + eps * (_root_.BoseGases.a v) with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; positivity
  set C : ℝ := max 1 (max (4 * Ks)
    (8 * (Kc ^ 4 * (_root_.BoseGases.a v)
      / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)))) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCcred : 8 * (Kc ^ 4 * (_root_.BoseGases.a v)
      / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)) ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hτ1 : Kc ^ 2 / (4 * Ks ^ 2) ≤ 1 :=
    le_trans hτ2 (by have h := min_le_right eps 1; linarith)
  have hCκ : 4 * Ks ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨min (min ε₁ ε₂) (min ε₃ 1), C, lt_min (lt_min hε₁pos hε₂pos) (lt_min hε₃pos one_pos),
    hC0, ?_⟩
  intro μ hAdm n Φ u hu
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hAdm₃ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₃ :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨h16R, h16Rd, hdpos, hdle1, hVpos, hVcube, hVside, hmuV⟩ := hreg μ hAdm₁ u hu
  have hℓpos : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hμpos : 0 < μ := hAdm.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsm := hsmall μ hAdm₂
  have hInn : 0 ≤ Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.bI_nonneg v μ _
  have hχMnn : 0 ≤ Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.BoseFixB1B.chiCubeMassB_nonneg _ _ _ u
  have hD0 : 0 ≤ Submission.BoseGases.g0w0Mass (v := v) h := le_of_lt hDpos
  by_cases hn1 : n ≤ 1
  · have hA2z : Work.BoseFixB1B.bA2B h μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by
      rw [Work.BoseFixB1B.bA2B, Work.BoseFixB1.boxA2]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      exfalso
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact hne (Fin.ext (by omega))
    have h1 : 0 ≤ (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h
        + eps * (_root_.BoseGases.a v))
        * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
        * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u := by
      have h2 : 0 ≤ (1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h + eps * (_root_.BoseGases.a v) := by
        have := hav.le; positivity
      have h3 : 0 ≤ ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2) := by positivity
      have h4 : 0 ≤ (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h
          + eps * (_root_.BoseGases.a v)) := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg h4 h3) hInn) hχMnn
    have h5 : 0 ≤ Work.BoseFixB1B.bSpectralCubeB v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      rw [Work.BoseFixB1B.bSpectralCubeB]
      exact Work.BoseFixB1.tBwordKinInd_nonneg _
    have h6 : 0 ≤ C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      have hμn : 0 ≤ μ + (n : ℝ) / Work.BoseFixB1.bV v μ u :=
        add_nonneg hμpos.le (div_nonneg (Nat.cast_nonneg n) hVpos.le)
      have hQ : 0 ≤ Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u :=
        Work.BoseFixB1.bQ_nonneg v μ _ u
      exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμn) hQ
    have h7 : 0 ≤ C * (_root_.BoseGases.a v) * μ
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμpos.le) hInn
    rw [hA2z]
    linarith
  · have hn2 : 2 ≤ n := by omega
    by_cases hI0 : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0
    · obtain ⟨_hflat0, hQ0, _hA2old⟩ :=
        Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero (h := h) Φ.contDiff hI0
      have hA20 : Work.BoseFixB1B.bA2B h μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 :=
        bA2B_eq_zero_of_bI_eq_zero h Φ.contDiff hI0
      have hspec : 0 ≤ Work.BoseFixB1B.bSpectralCubeB v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
        rw [Work.BoseFixB1B.bSpectralCubeB]
        exact Work.BoseFixB1.tBwordKinInd_nonneg _
      have h1 : (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h
          + eps * (_root_.BoseGases.a v))
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
          * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u = 0 := by
        rw [hI0]; ring
      have h4 : C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by rw [hQ0]; ring
      have h5 : C * (_root_.BoseGases.a v) * μ
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0 := by rw [hI0]; ring
      rw [hA20, h1, h4, h5]
      linarith [hspec]
    · -- ## the main case
      have hIpos : 0 < Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
        lt_of_le_of_ne hInn (Ne.symm hI0)
      obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.cast_add, Nat.cast_one]
      -- ### the normalisation `Ψ := Φ/√(∫Φ²)`
      set t : ℝ := Real.sqrt (Work.BoseFixB1.bI v μ
        (Φ : Submission.BoseGases.X (N + 1) → ℝ)) with ht
      have htpos : 0 < t := Real.sqrt_pos.mpr hIpos
      have ht2 : t ^ 2 = Work.BoseFixB1.bI v μ
          (Φ : Submission.BoseGases.X (N + 1) → ℝ) := Real.sq_sqrt hInn
      have htne : t ≠ 0 := ne_of_gt htpos
      set Ψ : Submission.BoseGases.X (N + 1) → ℝ := fun x => t⁻¹ * Φ x with hΨdef
      have hΦeq : (Φ : Submission.BoseGases.X (N + 1) → ℝ) = fun x => t * Ψ x := by
        funext x; rw [hΨdef]; field_simp
      have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
        rw [hΨdef]; exact Φ.contDiff.const_smul t⁻¹
      have hbIval : Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) = 1 := by
        have hstep : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (fun x => t * Ψ x) x ^ 2)
            = t ^ 2 * (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
                (Ψ x) ^ 2) := by
          rw [← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
        have h2 : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (Φ : Submission.BoseGases.X (N + 1) → ℝ) x ^ 2) = t ^ 2 := by
          change Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) = t ^ 2
          exact ht2.symm
        rw [← hΦeq, h2] at hstep
        have h3 : t ^ 2 * (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (Ψ x) ^ 2) = t ^ 2 * 1 := by rw [← hstep, mul_one]
        have h4 := mul_left_cancel₀ (pow_ne_zero 2 htne) h3
        change (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
          (Ψ x) ^ 2) = 1 at h4
        exact h4
      have hnormΨ : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
          (Ψ x) ^ 2) = 1 := by rw [← hbIval, Work.BoseFixB1.bI]
      -- ### the sliding data
      set ℓ : ℝ := Work.BoseFixB1.bSide v μ with hℓdef
      set dd : ℝ := Work.BoseFixB1.bD v μ with hddef
      set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
      set A : Set E3 := Work.BoseFixB1.bA v μ u with hAdef
      set Mv : ℕ := Work.BoseFixB1.bM v μ with hMvdef
      set χ : E3 → ℝ := Work.BoseFixB1B.chiCubeB Mv ℓ dd u with hχdef
      set 𝒲 : E3 → ℝ := Work.BoseFixB1B.wSmallInner Mv ℓ dd (Submission.BoseGases.g0 v h)
        with h𝒲def
      set c : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hcdef
      set Xw : ℝ := ∫ z : E3, (χ z) ^ 2 with hXwdef
      set Xp : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).X with hXpdef
      have hMv48 : Mv = Work.BoseBox.mValue := by rw [hMvdef]; rfl
      have hℓpos' : 0 < ℓ := by rw [hℓdef]; exact hℓpos
      have hdpos' : 0 < dd := by rw [hddef]; exact hdpos
      have hdle1' : dd ≤ 1 := by rw [hddef]; exact hdle1
      have hVpos' : 0 < V := by rw [hVdef]; exact hVpos
      have hcpos : 0 < c := by rw [hcdef]; exact Work.BoseFixB1S.sbCut_pos hμpos hav
      have hAmeas : MeasurableSet A := by
        show MeasurableSet (Submission.BoseGases.dlBox ℓ dd u)
        exact Work.SmallBoxSliding.measurableSet_dlBox ℓ dd u
      have hAsub : A ⊆ Submission.BoseGases.acube ℓ := by
        show Submission.BoseGases.dlBox ℓ dd u ⊆ Submission.BoseGases.acube ℓ
        exact Work.SmallBoxSliding.dlBox_subset_acube ℓ dd u
      have hAvol : V = (MeasureTheory.volume A).toReal := by
        show Work.SmallBoxSliding.boxMass ℓ dd u
            = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ dd u)).toReal
        exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ dd u
      have hMv5 : 5 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hχc2 : ContDiff ℝ 2 χ := by
        show ContDiff ℝ 2 (Work.BoseFixB1B.chiCubeB Mv ℓ dd u)
        exact chiCubeB_contDiff_two Mv ℓ dd u
      have hχs : HasCompactSupport χ := by
        show HasCompactSupport (Work.BoseFixB1B.chiCubeB Mv ℓ dd u)
        exact chiCubeB_hasCompactSupport (M := Mv) hℓpos' u
      have hχsupp : ∀ z, z ∉ A → χ z = 0 := by
        intro z hz
        show Work.BoseFixB1B.chiCubeB Mv ℓ dd u z = 0
        exact chiCubeB_eq_zero_of_notMem_dlBox (M := Mv) hℓpos' hdpos' u hz
      have hχnn : ∀ z, 0 ≤ χ z := fun z => by
        show 0 ≤ Work.BoseFixB1B.chiCubeB Mv ℓ dd u z
        exact chiCubeB_nonneg Mv ℓ dd u z
      have hκχ : ∀ z, |χ z| ≤ 1 := fun z => by
        show |chiCubeB Mv ℓ dd u z| ≤ 1
        exact chiCubeB_abs_le_one Mv ℓ dd u z
      -- ### the kernel data
      have h16Rℓ : 16 * R ≤ ℓ := by rw [hℓdef]; exact h16R
      have h16Rℓd : 16 * R ≤ ℓ * dd := by rw [hℓdef, hddef]; exact h16Rd
      obtain ⟨hsup0, hfin0, _hM10⟩ := hKcbound (ℓ := ℓ) (d := dd) hℓpos' hdpos' h16Rℓ h16Rℓd
      have h𝒲int : MeasureTheory.Integrable 𝒲 := by
        rw [h𝒲def]
        exact Work.BoseFixB1S.wSmallInner_integrable16 h hR hv hv1 hvrad hv_supp
          (le_trans (by norm_num) hMv5) hℓpos' hdpos' h16Rℓ h16Rℓd
      have hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Kc * (_root_.BoseGases.a v) := by
        intro q
        rw [h𝒲def]
        exact hsup0 q
      have hfin : MeasureTheory.Integrable (fun q : E3 =>
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
        rw [h𝒲def]; exact hfin0
      -- the sharp Newtonian mass at the window
      have hχR0 : R ≤ ℓ * Submission.BoseGases.chiR0 := by
        have h := (hε₃ μ hμpos hAdm₃).2
        rwa [Work.BoseFixGlue.ℓB] at h
      have hJ0 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)
          ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) * D := by
        rw [h𝒲def, hDdef]
        exact hK1sh (ℓ := ℓ) (d := dd) hℓpos' hdpos' (by linarith [h16Rℓd]) hχR0
      -- ### the two integrability inputs of the chain
      have hBle : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q / V|
          ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * (_root_.BoseGases.a v) / V := by
        intro q
        have h := Work.BoseFixB1B.pairRung.hBle_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (K := Kc) (𝒲 := 𝒲)
          hVpos' hav.le hKsKc hsup q
        have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
          rw [Nat.cast_add, Nat.cast_one]
          congr 1
          ring
        rw [hcast] at h
        exact h
      have hIntQ : MeasureTheory.Integrable (fun q : E3 =>
          (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * (_root_.BoseGases.a v) / V
            - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * (_root_.BoseGases.a v) / V) ^ 2
              - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2) := by
        have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (𝒲 := 𝒲) hVpos' hKs0 hav hcpos.le h𝒲int hfin
        have hIK : MeasureTheory.Integrable (fun q : E3 =>
            (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
              (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * (_root_.BoseGases.a v) / V)) := by
          refine hh.congr (Filter.Eventually.of_forall fun q => ?_)
          have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
            rw [Nat.cast_add, Nat.cast_one]
            congr 1
            ring
          rw [hcast]
        exact intQ_of_intK (N := N) (V := V) (Ks := Ks) (av := _root_.BoseGases.a v) (c := c)
          (𝒲 := 𝒲) hVpos' hKs0 hav hBle hIK
      have hintP : MeasureTheory.Integrable (fun q : E3 =>
          (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * (_root_.BoseGases.a v) / V) *
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) := by
        have hfsK : MeasureTheory.Integrable (fun q : E3 =>
            Submission.BoseGases.fsKinCoeff c ‖q‖ *
              Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          chiCubeB_fsKinPGenIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
            hℓpos' hdpos' hdle1' hMv5 u hVpos' hcpos hΨcd
        have hP : MeasureTheory.Integrable (fun q : E3 =>
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          (chiCubeB_windowIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
            hℓpos' hdpos' hdle1' hMv5 u hVpos' hΨcd).1
        have h1 := hfsK.const_mul (1 / ((N : ℝ) + 1 + 1))
        have h2 := hP.const_mul (2 * Ks * (_root_.BoseGases.a v) / V)
        refine (h1.add h2).congr (Filter.Eventually.of_forall fun q => ?_)
        simp only [Pi.add_apply]
        ring
      have hintR : MeasureTheory.Integrable (fun q : E3 =>
          (1 / V) * Submission.BoseGases.pairW 𝒲 q *
            Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q) := by
        have hh : MeasureTheory.Integrable (fun q : E3 =>
            Submission.BoseGases.pairW 𝒲 q * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q) :=
          Work.BoseFixB1B.pairRung.winModeRGenMulPairWIntegrable (n := N + 1) (a := ℓ) (volA := V)
            hℓpos' hVpos' hAmeas hAsub hAvol hχc2 hχs hχsupp (fun z => hκχ z) h𝒲int hΨcd
        have h2 : (fun q : E3 => (1 / V) * (Submission.BoseGases.pairW 𝒲 q
              * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q))
            = fun q : E3 => (1 / V) * Submission.BoseGases.pairW 𝒲 q
              * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q := by
          funext q; ring
        rw [← h2]
        exact hh.const_mul (1 / V)
      have hIntK : MeasureTheory.Integrable (fun q : E3 =>
          (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
            (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * (_root_.BoseGases.a v) / V)) := by
        have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (𝒲 := 𝒲) hVpos' hKs0 hav hcpos.le h𝒲int hfin
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      -- ### the sharp chain
      have hchain := chainA2SharpBeps (N := N) (by omega) (ℓ := ℓ) (volA := V) (c := c)
        (Kc := Kc) (Ks := Ks) (av := _root_.BoseGases.a v) (κ := 1) (μ := μ) (δ := δ)
        (Ac := A) (χ := χ) (𝒲 := 𝒲) (Ψ := Ψ)
        hℓpos' hVpos' hKs0 hav hcpos hKc0 hδpos hδle hKsKc hμpos.le hAmeas hAsub hAvol hχc2 hχs
        hχsupp hχnn hκχ hΨcd hnormΨ h𝒲int hsup hfin hintP hintR hIntK hIntQ
      -- ### the row arithmetic
      have hXw0 : 0 ≤ Xw := by rw [hXwdef]; exact integral_nonneg (fun z => sq_nonneg _)
      have hXwle : Xw ≤ V := by
        rw [hXwdef]
        show (∫ z : E3, (chiCubeB Mv ℓ dd u z) ^ 2) ≤ Work.SmallBoxSliding.boxMass ℓ dd u
        exact chiCubeMassB_le_boxMass Mv hℓpos' hdpos' u
      have hSle : Work.BoseFixB1S.boxFlatCount V ℓ A Ψ ≤ (N : ℝ) + 1 := by
        have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := N + 1) hℓpos' hVpos' hAmeas hAsub
          hAvol hΨcd.continuous
        rw [hnormΨ, mul_one] at hh
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Ψ := by
        rw [Work.BoseFixB1S.boxFlatCount]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hJ00 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
        refine mul_nonneg (by positivity) ?_
        exact integral_nonneg (fun q => div_nonneg (sq_nonneg _) (sq_nonneg _))
      have hmain : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
          ≤ 2 * (1 - θ) * c0 / D := by
        have hδ₀ : K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2) ≤ min eps 1 / 32 := by
          have h := hsmall μ hAdm₂
          simpa [hℓdef, hddef] using h
        set x : ℝ := min eps 1 / 32 with hxdef
        have hx0 : 0 ≤ x := by rw [hxdef]; positivity
        have hxle : x ≤ eps / 32 := by
          rw [hxdef]
          have h := min_le_left eps 1
          linarith
        have hxsmall : x ≤ 1 / 4 := by
          rw [hxdef]
          have h := min_le_right eps 1
          linarith
        have hA : 1 + Kc ^ 2 / (4 * Ks ^ 2) ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hτ2 1
        have hB : 1 + 8 * δ ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hδsmall 1
        have hC : 1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2) ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hδ₀ 1
        have hcube : (1 + x) * (1 + x) * (1 + x) ≤ 1 + 4 * x := by
          have hx2 : x * x ≤ x / 4 := by nlinarith [hx0, hxsmall]
          have hx3 : x * x * x ≤ x / 16 := by nlinarith [hx2, hxsmall, hx0]
          nlinarith [hx0, hxsmall, hx2, hx3]
        have h4 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) ≤ (1 + x) * (1 + x) :=
          mul_le_mul hA hB (by positivity) (by nlinarith [hx0])
        have h5 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))
            ≤ (1 + x) * (1 + x) * (1 + x) :=
          mul_le_mul h4 hC (by positivity) (by nlinarith [hx0])
        have hprod : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) ≤ 1 + eps / 8 := by
          have h6 : 4 * x ≤ eps / 8 := by linarith [hxle]
          have h7 : (1 + x) * (1 + x) * (1 + x) ≤ 1 + eps / 8 :=
            le_trans hcube (by linarith [h6])
          exact le_trans h5 h7
        have h34 : 1 + eps / 8 ≤ (1 - θ) * (c0 / D) := by
          have h6 : 1 + eps / 8 ≤ (1 - θ) * (1 + eps) := by linarith [hθsmall]
          have h7 : (1 + eps) ≤ c0 / D := by
            rw [hc0def, le_div_iff₀ hDpos]
            nlinarith [hDpos, hD0, hav, heps]
          have h8 : 0 ≤ 1 - θ := by linarith [hθle]
          calc 1 + eps / 8 ≤ (1 - θ) * (1 + eps) := by linarith [h6]
            _ ≤ (1 - θ) * (c0 / D) := mul_le_mul_of_nonneg_left h7 h8
        have h9 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) ≤ (1 - θ) * (c0 / D) :=
          le_trans hprod h34
        calc (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
              * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
            = 2 * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
                * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))) := by ring
          _ ≤ 2 * ((1 - θ) * (c0 / D)) := by linarith [h9]
          _ = 2 * (1 - θ) * c0 / D := by ring
      have hc6 : c ^ 6 * V ≤ μ := by
        have ha : (0:ℝ) < _root_.BoseGases.a v := hav
        have hXp0 : 0 < Xp := by
          rw [hXpdef]
          exact Work.BoseBox.fsXp_pos (mul_pos hμpos (pow_pos hav 3))
        have hXp1 : Xp ≤ 1 := by
          rw [hXpdef]
          exact Work.BoseBox.fsXp_le_one (mul_pos hμpos (pow_pos hav 3)) hμa3le (by norm_num)
        have hXpPow : Xp ^ 323 = μ * (_root_.BoseGases.a v) ^ 3 := by
          have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
          have h3 : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1) ^ 323
              = μ * (_root_.BoseGases.a v) ^ 3 := by
            show ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)) ^ 323
                = μ * (_root_.BoseGases.a v) ^ 3
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            norm_num
            try rw [Real.rpow_one]
          rw [hXpdef]
          exact h3
        have hc3 : c ^ 3 = ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 468 := by
          have h := Work.BoseFixB1S.sbCut_cube_eq (μ := μ) (α := _root_.BoseGases.a v) hav hμpos
          rw [← hcdef, ← hXpdef] at h
          exact h
        have hdl3 : (ℓ * dd) ^ 3 = (_root_.BoseGases.a v) ^ 3 * (Xp ^ 471)⁻¹ := by
          have h := Work.BoseFixB1.d_mul_sideAt_cube_eq (A := _root_.BoseGases.a v) (μ := μ)
            hav hμpos
          have h1 : ℓ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
            rw [hℓdef, Work.BoseFixB1.bSide]
          have h2 : dd = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
            rw [hddef, Work.BoseFixB1.bD]
          have h3 : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-471 : ℝ)
              = (Xp ^ 471)⁻¹ := by
            have ht0 : (0:ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
            have hXeq : Xp = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323) := by
              show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (1:ℝ)
                  = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323)
              rw [Work.BoseBox.fsXp]
            have hL : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-471 : ℝ)
                = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-471:ℝ)/323) := by
              rw [Work.BoseBox.fsXp]
            have hpow : ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323)) ^ 471
                = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((471:ℝ)/323) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht0)]
              norm_num
            rw [hL, hXeq,
              show (-471 : ℝ) / 323 = -((471 : ℝ) / 323) by ring,
              Real.rpow_neg (le_of_lt ht0), hpow]
          rw [h1, h2, mul_comm, h, h3]
        have hVle : V ≤ (ℓ * dd) ^ 3 := by rw [hVdef]; exact hVcube
        have h1 : c ^ 6 * V ≤ c ^ 6 * (ℓ * dd) ^ 3 :=
          mul_le_mul_of_nonneg_left hVle (by positivity)
        have heq : c ^ 6 * (ℓ * dd) ^ 3 = ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465 := by
          have hne : Xp ≠ 0 := ne_of_gt hXp0
          have hane : (_root_.BoseGases.a v) ≠ 0 := ne_of_gt hav
          rw [show c ^ 6 = (c ^ 3) ^ 2 by ring, hc3, hdl3, pow_two]
          field_simp <;> ring_nf
        have h1' : c ^ 6 * V ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465 := by
          rw [heq] at h1
          exact h1
        have h3 : Xp ^ 465 ≤ Xp ^ 323 :=
          pow_le_pow_of_le_one hXp0.le hXp1 (by norm_num)
        have h4 : ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 323 = μ := by
          rw [hXpPow]
          field_simp
        have h5 : 0 ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ := by positivity
        have h6 : ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465
            ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 323 :=
          mul_le_mul_of_nonneg_left h3 h5
        linarith [h1', h6, h4]
      have hK1pos : 0 ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) :=
        mul_nonneg (by norm_num)
          (add_nonneg (by norm_num) (mul_nonneg hK1s0 (add_nonneg (sq_nonneg _) (sq_nonneg _))))
      have hn0N : 0 ≤ (N : ℝ) + 1 := add_nonneg (Nat.cast_nonneg N) (by norm_num)
      have harith := epsRowArithBeps (n := (N : ℝ) + 1) (V := V)
        (av := _root_.BoseGases.a v) (c := c) (Kc := Kc) (Ks := Ks) (δ := δ)
        (K1 := 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))) (D := D) (c0 := c0)
        (S := Work.BoseFixB1S.boxFlatCount V ℓ A Ψ) (X := Xw)
        (mu := μ) (C := C) (J0 := ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)) (θ := θ)
        hVpos' hav hcpos hKs0 hKc0 hδpos hDpos hK1pos hc0pos hμpos hθpos hθle hτ1
        hn0N hS0 hSle hXw0 hXwle hJ00 hJ0 hC0 hc6 hmain hCcred
      -- ### transport back to `Φ`
      have hscSpec : Work.BoseFixB1B.bSpectralCubeB v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := by
        show Work.UBBInputs8.tBwordKinInd ℓ A V χ c (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
        rw [hΦeq]
        exact Work.BoseFixB1.tBwordKinInd_mul ℓ V χ c t Ψ
      have hscA2 : Work.BoseFixB1B.bA2B h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1B.bA2B h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1B.bA2B_mul h μ t Ψ u
      have hscQ : Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1.bQ_mul v μ t Ψ u
      have hscI : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) = t ^ 2 := by
        rw [hΦeq, Work.BoseFixB1.bI_mul, hbIval, mul_one]
      have hQeq : Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := rfl
      have hchiM : Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u = Xw := by
        show (∫ z : E3, (Work.BoseFixB1B.chiCubeB Mv ℓ dd u z) ^ 2) = Xw
        rw [hXwdef]
      have hA2Bunf : Work.BoseFixB1B.bA2B h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.BoseFixB1.boxA2 ℓ V A (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ := rfl
      have hspecΨ : Work.BoseFixB1B.bSpectralCubeB v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := rfl
      have hgoalΨ : -((1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
            * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ)
            * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ))
          ≤ Work.BoseFixB1B.bSpectralCubeB v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + Work.BoseFixB1B.bA2B h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        have h1 : Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) = 1 := hbIval
        have h2 : Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            = Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := hQeq
        have h3 : Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u = Xw := hchiM
        have h4 : Work.BoseFixB1B.bSpectralCubeB v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            = Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := rfl
        rw [h1, h2, h3, h4, hA2Bunf]
        -- the credit row pays the chain's `A₁`-loss, since `C ≥ 4 K_s`
        have hcred2 : (4 * Ks * 1 ^ 2) * (_root_.BoseGases.a v)
            * ((μ + (((N : ℝ) + 1) / V)) * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ)
            ≤ C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
          have h6 : 0 ≤ (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
            have h7 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
              rw [Work.UBBInputs8.cnPlusBoxInd]
              exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
            have h8 : 0 ≤ μ + (((N : ℝ) + 1) / V) :=
              add_nonneg hμpos.le (div_nonneg (by positivity) hVpos'.le)
            exact mul_nonneg (mul_nonneg hav.le h8) h7
          have h9 : (4 * Ks * 1 ^ 2) ≤ C := by linarith [hCκ]
          calc (4 * Ks * 1 ^ 2) * (_root_.BoseGases.a v)
                * ((μ + (((N : ℝ) + 1) / V)) * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ)
              = (4 * Ks * 1 ^ 2) * ((_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ) := by ring
            _ ≤ C * ((_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ) :=
                mul_le_mul_of_nonneg_right h9 h6
            _ = C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by ring
        have hN2 : (N : ℝ) + 2 = (N : ℝ) + 1 + 1 := by ring
        have hXw' : (∫ z : E3, χ z ^ 2) = Xw := hXwdef.symm
        rw [hN2, hXw'] at hchain
        linarith [hchain, harith, hcred2]
      -- ### scale back
      have hgoal_eq : -((1 / 2) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h
              + eps * (_root_.BoseGases.a v))
            * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ))
          = t ^ 2 * (-((1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
              * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ)
              * Work.BoseFixB1B.chiCubeMassB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u
            + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ))) := by
        rw [hscI, hscQ, hbIval]
        rw [hc0def, hDdef]
        ring
      have hrhs : Work.BoseFixB1B.bSpectralCubeB v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + Work.BoseFixB1B.bA2B h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * (Work.BoseFixB1B.bSpectralCubeB v μ
              (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + Work.BoseFixB1B.bA2B h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u) := by
        rw [hscSpec, hscA2, hspecΨ]; ring
      rw [hgoal_eq, hrhs]
      exact mul_le_mul_of_nonneg_left hgoalΨ (by positivity)


end Work.BoseFixB1B
