import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero
import Submission.Work.BoseFixB1B.pairRung.chainInputs
import Submission.Work.BoseFixB1B.pairRung.modeBoundPointwise
import Submission.Work.BoseFixB1B.pairRung.term1
import Submission.Work.BoseFixB1B.pairRung.term2C2
import Submission.Work.BoseFixB1B.pairRung.winModeRGenMulPairWIntegrable
import Submission.Work.BoseFixB1B.perBoxFTotalInterfaces
import Submission.Work.BoseFixB1B.slidingChainArithB
import Submission.Work.BoseFixB1S.admGoodSetRegime2
import Submission.Work.BoseFixB1S.boxFlatCount_le_NB1
import Submission.Work.BoseFixB1S.nuPairWNuIntegrable
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
import Submission.Work.BoseFixB1S.sbCut_cube_eq
import Submission.Work.BoseFixB1S.wSmallInner_integrable16
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.slidingBogPortProved` — the sliding Bogoliubov port, **proved**

**HOLDER / PROVENANCE.**  This is a verbatim copy (up to the renaming of the two public
declarations) of `Submission/Work/BoseFixB1B/slidingBogPort_holds.lean`, whose *only* gap was the
private pure-real lemma `slidingChainArith_local`; that lemma is now **proved** as
`Work.BoseFixB1B.slidingChainArithB` (`Submission/Work/BoseFixB1B/slidingChainArithB.lean`), so the
port below is `sorry`-free and axiom-clean.  The original file is left untouched (its owner may
close it the same way with a one-line change); the copy exists so that the fleet can *import* the
port immediately: consumers that need `SlidingBogPort v h` can use
`Work.BoseFixB1B.slidingBogPort_proved` (and `Work.BoseFixB1B.chainA2B` for the one-box chain).

Original header follows.


# `Submission.Work.BoseFixB1B.slidingBogPort_holds` — the sliding Bogoliubov port

The target is `Work.BoseFixB1B.SlidingBogPort v h` (FS `lm:appbogolubov`,
`final_v2.tex` l. 3762–3780) in the spelling of `perBoxFTotalInterfaces`.

## The route

1. `chainA2B` — FS's Bogoliubov chain at one box, in the vocabulary of
   `Work.BoseFixB1S.chainIntegralQdep`: for a *normalised* state `Ψ : X (N+1)`,

       boxA2 ≥ -S·X·(c³K_s(a v)/(3π²V) + 4(N+2)K_s PM/V²) - tBwordKinInd
                 - 4K_sκ²(a v)(μ+(N+1)/V)·n₊ .

   The bracket is the interior/exterior split of the chain's Term 1 (`term1IntegralBound`), the
   spectral word pays Term 2a and the credit pays Term 2b (`term2C2`).
2. `slidingBogPort_holds` — any `BoxState` is scaled to `∫Φ² = 1` (the words are homogeneous of
   degree two: `bA2_mul`/`bQ_mul`/`bI_mul`/`tBwordKinInd_mul`), the chain is applied at FS's
   parameters, and the three rows of the target cover the chain's three rows.  The interior row is
   split in two cases: for `N+2 ≥ Θ := 4c³VK_s(a v)/(3π²(1+η)D)` the mass row pays it, and
   otherwise `n < Θ` and the row `C·a·μ·∫Φ²` pays it, the constant `C` being finite because the
   comparison is `X^{937}·(stuff) ≤ C·a·μ·(stuff)` with `X ≤ 1` (using
   `Work.BoseFixB1S.sbCut_cube_eq`: `c³ = (a v)⁻³X^{468}`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.SmallBoxSliding Work.BoseBoxFix
  Work.BoseFixB1 Work.BoseFixB1S

/-- The `(2π)^{-3}`-normalisation in the two spellings of the workspace. -/
private lemma pi_zpow_neg_three :
    ((2 * Real.pi) ^ (-(3 : ℤ)) : ℝ) = ((2 * Real.pi) ^ 3)⁻¹ := by
  rw [zpow_neg]; rfl

/-- **FS's Bogoliubov chain at one box** (the analytic heart of the port): the pairing word is
bounded below by the interior/exterior split of `chainIntegralQdep`'s first term, the spectral
word and the excited-count credit.

The three integrability hypotheses are exactly the chain's, and are discharged at the sliding
window in `slidingBogPort_holds` (the window `chiSmallB` is only `C^{M-1}`, so the `C^∞`-forms of
`pairRung` cannot be used there). -/
theorem chainA2B {N : ℕ} (hN : 1 ≤ N) {ℓ volA c Ks av κ PM μ : ℝ}
    {A : Set E3} {χ 𝒲 : E3 → ℝ} {Ψ : Submission.BoseGases.X (N + 1) → ℝ}
    (hℓ : 0 < ℓ) (hvolpos : 0 < volA) (hKs : 0 < Ks) (hav : 0 < av) (hPM : 0 < PM) (hc : 0 < c)
    (hμnn : 0 ≤ μ)
    (hAcm : MeasurableSet A) (hAcsub : A ⊆ Submission.BoseGases.acube ℓ)
    (hvol : volA = (MeasureTheory.volume A).toReal)
    (hχc2 : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, |χ z| ≤ κ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hnorm : (∫ x in Submission.BoseGases.abox (N + 1) ℓ, (Ψ x) ^ 2) = 1)
    (h𝒲int : MeasureTheory.Integrable 𝒲)
    (hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Ks * av)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2) ≤ 2 * Ks * PM)
    (hfin : MeasureTheory.Integrable (fun q : E3 =>
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2))
    (hintP : MeasureTheory.Integrable (fun q : E3 =>
      (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA) *
        Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q))
    (hintR : MeasureTheory.Integrable (fun q : E3 =>
      (1 / volA) * Submission.BoseGases.pairW 𝒲 q *
        Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q))
    (hIntK : MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q / volA) ^ 2 /
        (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA))) :
    Work.BoseFixB1.boxA2 ℓ volA A (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      ≥ - (Work.BoseFixB1S.boxFlatCount volA ℓ A Ψ) * (∫ z : E3, (χ z) ^ 2)
            * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * volA)
                + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / volA ^ 2)
        - Work.UBBInputs8.tBwordKinInd ℓ A volA χ c Ψ
        - (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ A volA Ψ) := by
  classical
  set 𝒜 : E3 → ℝ := fun q => 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
    + 2 * Ks * av / volA with h𝒜
  set ℬ : E3 → ℝ := fun q => Submission.BoseGases.pairW 𝒲 q / volA with hℬ
  set S : ℝ := Work.BoseFixB1S.boxFlatCount volA ℓ A Ψ with hS
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
  have hpair : Work.BoseFixB1.boxA2 ℓ volA A (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      = (2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q *
            (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q) := by
    have h := Work.BoseFixB1S.boxPairIntGenC2' (n := N + 1) (by omega) (a := ℓ) (volA := volA)
      hℓ hAcm hAcsub hvol hvolpos hχc2 hχs hχsupp h𝒲int hΨ
    rw [h, pi_zpow_neg_three]
  have hB : ∀ q : E3, ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := fun q => by rw [hℬ]
  have hBle : ∀ q : E3, |ℬ q| ≤ 𝒜 q := by
    intro q
    have h := Work.BoseFixB1B.pairRung.hBle_of (n := N + 1) (V := volA) (Ks := Ks) (av := av)
      (c := c) (K := Ks) (𝒲 := 𝒲) hvolpos hav.le (by linarith) hsup q
    simp only [Nat.cast_add, Nat.cast_one] at h
    have h1 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
    have h2 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    rw [h1, h2]
    exact h
  have hmod : ∀ q : E3,
      -(((𝒜 q - Real.sqrt (𝒜 q ^ 2 - ℬ q ^ 2)) / 2)
          * ((∫ z in A, (Work.BoseFixB1.boxWinModeReGen volA A χ q z) ^ 2)
              + (∫ z in A, (Work.BoseFixB1.boxWinModeImGen volA A χ q z) ^ 2))
          * (Work.BoseFixB1S.boxFlatCount volA ℓ A Ψ))
        ≤ 𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q
          + ℬ q * Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q := by
    intro q
    have h := Work.BoseFixB1B.pairRung.modeBoundPointwise (n := N) (q := q) (a := ℓ)
      (Acoef := 𝒜 q) (B := ℬ q) (volA := volA) (κ := κ) (Ac := A) (χ := χ) (Ψ := Ψ)
      hℓ hAcm hAcsub hvol hvolpos hχc2.continuous hχs hχsupp hκ
      (le_trans (abs_nonneg (χ 0)) (hκ 0)) hΨ.continuous (hApos q) (hBle q)
    exact h
  have hXq : ∀ q : E3,
      (∫ z in A, (Work.BoseFixB1.boxWinModeReGen volA A χ q z) ^ 2)
          + (∫ z in A, (Work.BoseFixB1.boxWinModeImGen volA A χ q z) ^ 2) ≤ X := by
    intro q
    have h := Work.BoseFixB1S.winMode_mass_le (volA := volA) (Ac := A) hAcm hvol hvolpos
      hχc2.continuous hχs hχsupp q
    have hX1 : X = ∫ z : E3, (χ z) ^ 2 := by rw [hX]
    rw [hX1]
    exact h
  have hintP' : MeasureTheory.Integrable (fun q : E3 =>
      𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q) := by
    refine hintP.congr (Filter.Eventually.of_forall fun q => ?_)
    have h2 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * av / volA := by rw [h𝒜]
    simp only []
    rw [h2]
  have hintR' : MeasureTheory.Integrable (fun q : E3 =>
      ℬ q * Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q) := by
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
  -- ## the chain
  have hchain := Work.BoseFixB1S.chainIntegralQdep (N := N) (a := ℓ) (volA := volA) (S := S)
    (X := X) (Ac := A) (χ := χ) (Ψ := Ψ) (𝒲 := 𝒲) (B := ℬ) (Acoef := 𝒜)
    hApos hS0 hX0 hpair hB hBle hmod hXq hintP' hintR' hIntK'
  -- ## Term 1: the interior/exterior split of the chain's first term
  have hI : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3, ℬ q ^ 2 / (2 * 𝒜 q))
      ≤ c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * volA)
        + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / volA ^ 2 := by
    have hbase := Work.BoseFixB1B.pairRung.term1IntegralBound (N := N + 1) (Ks := Ks) (a := av)
      (c := c) (V := volA) (PM := PM) (g := fun q : E3 => Submission.BoseGases.pairW 𝒲 q)
      hvolpos hc hKs hav hsup hM1
    simp only [Nat.cast_add, Nat.cast_one] at hbase
    have hL : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3, ℬ q ^ 2 / (2 * 𝒜 q))
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
            (Submission.BoseGases.pairW 𝒲 q) ^ 2 / (volA ^ 2 * 2 *
              (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * av / volA)) := by
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      have h2 : ℬ q = Submission.BoseGases.pairW 𝒲 q / volA := by rw [hℬ]
      have h3 : 𝒜 q = 1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * av / volA := by rw [h𝒜]
      simp only []
      rw [h2, h3, div_pow, div_div]
      ring
    rw [hL]
    exact hbase
  -- ## Term 2: the spectral word and the credit
  have hJ : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
        𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q)
      ≤ Work.UBBInputs8.tBwordKinInd ℓ A volA χ c Ψ
        + (4 * Ks * κ ^ 2) * av * ((μ + (((N : ℝ) + 1) / volA))
            * Work.UBBInputs8.cnPlusBoxInd ℓ A volA Ψ) := by
    have h := Work.BoseFixB1B.pairRung.term2C2 (N := N + 1) (a := ℓ) (volA := volA) (V := volA)
      (Ks := Ks) (κ := κ) (μ := μ) (av := av) (c := c) (Ac := A) (χ := χ) (Ψ := Ψ)
      (hΨc := hΨ)
      hℓ hAcm hAcsub hvol hvolpos hχc2 hχs hχsupp hχnn hc hvolpos hKs.le hav.le hμnn hκ
    simp only [Nat.cast_add, Nat.cast_one] at h
    have hL : ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3,
          𝒜 q * Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q)
        = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
            (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / volA)
              * Work.BoseFixB1.boxWinModePGen ℓ volA A χ Ψ q) := by
      rw [pi_zpow_neg_three]
    rw [hL]
    exact h
  -- ## combine
  have hSX : 0 ≤ S * X := mul_nonneg hS0 hX0
  have hI2 : S * X * ((2 * Real.pi) ^ (-(3 : ℤ)) * ∫ q : E3, ℬ q ^ 2 / (2 * 𝒜 q))
      ≤ S * X * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * volA)
          + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / volA ^ 2) :=
    mul_le_mul_of_nonneg_left hI hSX
  linarith [hchain, hI2, hJ]


/-- **The sliding Bogoliubov port** (FS `lm:appbogolubov` at the sliding box). -/
theorem slidingBogPort_proved {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1B.SlidingBogPort v h := by
  classical
  obtain ⟨K, hK0, hKbound⟩ :=
    Work.BoseFixB1S.nuPairWNuIntegrable (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε₁, hε₁pos, hreg⟩ :=
    Work.BoseFixB1S.admGoodSetRegime2 (v := v) h hv hv1 hvrad hR hv_supp hav
  set Ks : ℝ := max K 1 with hKsdef
  have hKs0 : (0 : ℝ) < Ks := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  have hKle : K ≤ Ks := le_max_left K 1
  set κ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
    Work.BoseBox.mValue with hκdef
  have hκ0 : 0 ≤ κ := mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
    (Submission.BoseGases.chiSmallDecay_nonneg _)
  set D : ℝ := Submission.BoseGases.g0w0Mass (v := v) h with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, ← Work.BoseFixB1B.PairMass_eq_g0w0Mass]
    exact Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav
  set PM : ℝ := D / 2 with hPMdef
  have hPMpos : 0 < PM := by rw [hPMdef]; positivity
  have hKsPM : 2 * Ks * PM = Ks * D := by rw [hPMdef]; ring
  set η : ℝ := 8 * Ks + 1 with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hηK : 8 * Ks ≤ 1 + η := by rw [hηdef]; linarith
  set C : ℝ := max (4 * Ks * κ ^ 2)
    (4 * κ ^ 2 * Ks ^ 2 * (_root_.BoseGases.a v) / (9 * Real.pi ^ 4 * (1 + η) * D)) + 1 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCκ : 4 * Ks * κ ^ 2 ≤ C := by
    have h' := le_max_left (4 * Ks * κ ^ 2)
      (4 * κ ^ 2 * Ks ^ 2 * (_root_.BoseGases.a v) / (9 * Real.pi ^ 4 * (1 + η) * D))
    rw [hCdef]; linarith
  have hCint : 4 * κ ^ 2 * Ks ^ 2 * (_root_.BoseGases.a v)
        / (9 * Real.pi ^ 4 * (1 + η) * D) ≤ C := by
    have h' := le_max_right (4 * Ks * κ ^ 2)
      (4 * κ ^ 2 * Ks ^ 2 * (_root_.BoseGases.a v) / (9 * Real.pi ^ 4 * (1 + η) * D))
    rw [hCdef]; linarith
  refine ⟨min ε₁ 1, η, C, lt_min hε₁pos one_pos, hη0, hC0, ?_⟩
  intro μ hAdm n Φ u hu
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left ε₁ 1), hAdm.2.2⟩
  obtain ⟨h16R, h16Rd, hdpos, hdle1, hVpos, hVcube, hVside, hmuV⟩ := hreg μ hAdm₁ u hu
  have hℓpos : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hμpos : 0 < μ := hAdm.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right ε₁ 1)
  have hInn : 0 ≤ Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.bI_nonneg v μ _
  have hχMnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  have hD0 : 0 ≤ Submission.BoseGases.g0w0Mass (v := v) h := le_of_lt (by
    rw [← Work.BoseFixB1B.PairMass_eq_g0w0Mass]
    exact Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav)
  by_cases hn1 : n ≤ 1
  · -- ## the degenerate case `n ≤ 1`
    have hA2z : Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by
      rw [Work.BoseFixB1.bA2, Work.BoseFixB1.boxA2]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      exfalso
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact hne (Fin.ext (by omega))
    have h1 : 0 ≤ (1 / 2 : ℝ) * (1 + η) * Submission.BoseGases.g0w0Mass (v := v) h
        * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u := by
      have hη1 : 0 ≤ (1 / 2 : ℝ) * (1 + η) := by positivity
      have hfac : 0 ≤ ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2) := by
        positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hη1 hD0) hfac) hInn) hχMnn
    have h2 : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      rw [Work.BoseFixB1S.bSpectralCube]
      exact Work.BoseFixB1.tBwordKinInd_nonneg _
    have h3 : 0 ≤ Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u :=
      Work.BoseFixB1.bQ_nonneg v μ _ u
    have h4 : 0 ≤ C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      have hμn : 0 ≤ μ + (n : ℝ) / Work.BoseFixB1.bV v μ u :=
        add_nonneg hμpos.le (div_nonneg (Nat.cast_nonneg n) hVpos.le)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμn) h3
    have h5 : 0 ≤ C * (_root_.BoseGases.a v) * μ
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμpos.le) hInn
    rw [hA2z]
    linarith
  · have hn2 : 2 ≤ n := by omega
    by_cases hI0 : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0
    · -- ## the vanishing case `∫Φ² = 0`
      obtain ⟨_hflat0, hQ0, hA20⟩ :=
        Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero (h := h) Φ.contDiff hI0
      have hspec : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
        rw [Work.BoseFixB1S.bSpectralCube]
        exact Work.BoseFixB1.tBwordKinInd_nonneg _
      have h1 : (1 / 2 : ℝ) * (1 + η) * Submission.BoseGases.g0w0Mass (v := v) h
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u = 0 := by
        rw [hI0]; ring
      have h4 : C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by
        rw [hQ0]; ring
      have h5 : C * (_root_.BoseGases.a v) * μ
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
        rw [hI0]; ring
      rw [hA20, h1, h4, h5]
      linarith [hspec]
    · -- ## the main case
      have hIpos : 0 < Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
        lt_of_le_of_ne hInn (Ne.symm hI0)
      obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.cast_add, Nat.cast_one]
      -- ### the normalisation `Ψ := Φ/√(∫Φ²)`
      set t : ℝ := Real.sqrt (Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ))
        with ht
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
        change (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1
          at h4
        exact h4
      have hnormΨ : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
          (Ψ x) ^ 2) = 1 := by rw [← hbIval, Work.BoseFixB1.bI]
      -- ### the sliding data
      set ℓ : ℝ := Work.BoseFixB1.bSide v μ with hℓdef
      set dd : ℝ := Work.BoseFixB1.bD v μ with hddef
      set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
      set A : Set E3 := Work.BoseFixB1.bA v μ u with hAdef
      set Mv : ℕ := Work.BoseFixB1.bM v μ with hMvdef
      set χ : E3 → ℝ := Submission.BoseGases.chiSmallB Mv ℓ dd u with hχdef
      set 𝒲 : E3 → ℝ := Work.BoseFixB1B.wSmallInner Mv ℓ dd (Submission.BoseGases.g0 v h)
        with h𝒲def
      set c : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hcdef
      set Xw : ℝ := ∫ z : E3, (χ z) ^ 2 with hXwdef
      set Θ : ℝ := 4 * c ^ 3 * V * Ks * (_root_.BoseGases.a v)
        / (3 * Real.pi ^ 2 * (1 + η) * D) with hΘdef
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
      have hMv1 : 1 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hMv3 : 3 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hMv5 : 5 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hχc2 : ContDiff ℝ 2 χ := by
        show ContDiff ℝ 2 (Submission.BoseGases.chiSmallB Mv ℓ dd u)
        exact Work.BoseFixB1.chiSmallB_contDiff_two hMv3 u
      have hχs : HasCompactSupport χ := by
        show HasCompactSupport (Submission.BoseGases.chiSmallB Mv ℓ dd u)
        exact Submission.BoseGases.chiSmallB_hasCompactSupport hMv1 hℓpos' u
      have hχsupp : ∀ z, z ∉ A → χ z = 0 := by
        intro z hz
        show Submission.BoseGases.chiSmallB Mv ℓ dd u z = 0
        exact Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hMv1 hℓpos' hdpos' u hz
      have hχnn : ∀ z, 0 ≤ χ z := fun z => by
        show 0 ≤ Submission.BoseGases.chiSmallB Mv ℓ dd u z
        exact Submission.BoseGases.chiSmallB_nonneg Mv ℓ dd u z
      have hκχ : ∀ z, |χ z| ≤ κ := by
        intro z
        show |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
            ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
        have h1 := Work.SmallBoxSliding.abs_chiSmallB_le (M := Mv) (ℓ := ℓ) (d := dd) hMv1 u z
        have h2 : Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u)
            ≤ Submission.BoseGases.chiSmallDecay Mv := by
          have h3 := Submission.BoseGases.chiSmall_decay_coord_le_decay hMv1 ((ℓ * dd)⁻¹ • z - u)
          rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg Mv _)] at h3
        rw [hMv48]
        calc |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
            ≤ Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u) := h1
          _ ≤ Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
              mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
      -- ### the M1/Newtonian data at this box
      have h16Rℓ : 16 * R ≤ ℓ := by rw [hℓdef]; exact h16R
      have h16Rℓd : 16 * R ≤ ℓ * dd := by rw [hℓdef, hddef]; exact h16Rd
      obtain ⟨hsup0, hfin0, hM10⟩ := hKbound (ℓ := ℓ) (d := dd) hℓpos' hdpos' h16Rℓ h16Rℓd
      have h𝒲int : MeasureTheory.Integrable 𝒲 := by
        rw [h𝒲def]
        exact Work.BoseFixB1S.wSmallInner_integrable16 h hR hv hv1 hvrad hv_supp hMv1
          hℓpos' hdpos' h16Rℓ h16Rℓd
      have hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Ks * (_root_.BoseGases.a v) := by
        intro q
        rw [h𝒲def]
        exact le_trans (hsup0 q) (mul_le_mul_of_nonneg_right hKle hav.le)
      have hfin : MeasureTheory.Integrable (fun q : E3 =>
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
        rw [h𝒲def]; exact hfin0
      have hM1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) ≤ 2 * Ks * PM := by
        have h0 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
            Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled Mv
              (ℓ * dd) (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q ^ 2
              / ‖q‖ ^ 2) ≤ K * D := by
          rw [hDdef]; exact hM10
        have h0' : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
            Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled Mv
              (ℓ * dd) (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q ^ 2
              / ‖q‖ ^ 2) ≤ 2 * Ks * PM := by
          rw [hKsPM]
          exact le_trans h0 (mul_le_mul_of_nonneg_right hKle hDpos.le)
        rw [h𝒲def]
        exact h0'
      -- ### the three integrability inputs of the chain
      have hintP : MeasureTheory.Integrable (fun q : E3 =>
          (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * (_root_.BoseGases.a v) / V) *
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) := by
        have hfsK : MeasureTheory.Integrable (fun q : E3 =>
            Submission.BoseGases.fsKinCoeff c ‖q‖ *
              Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
            hℓpos' hdpos' hdle1' hMv5 u hVpos' hcpos hΨcd
        have hP : MeasureTheory.Integrable (fun q : E3 =>
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          (Work.BoseFixB1S.win.chiSmallB_windowIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
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
            hℓpos' hVpos' hAmeas hAsub hAvol hχc2 hχs hχsupp hκχ h𝒲int hΨcd
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
      -- ### the chain
      have hchain := chainA2B (N := N) (by omega) (ℓ := ℓ) (volA := V) (c := c) (Ks := Ks)
        (av := _root_.BoseGases.a v) (κ := κ) (PM := PM) (μ := μ) (A := A) (χ := χ) (𝒲 := 𝒲)
        (Ψ := Ψ) hℓpos' hVpos' hKs0 hav hPMpos hcpos hμpos.le hAmeas hAsub hAvol hχc2 hχs
        hχsupp hχnn hκχ hΨcd hnormΨ h𝒲int hsup hM1 hfin hintP hintR hIntK
      -- ### the arithmetic ledger
      have hXw0 : 0 ≤ Xw := by rw [hXwdef]; exact integral_nonneg (fun z => sq_nonneg _)
      have hXp0 : 0 ≤ Xp := by
        rw [hXpdef]
        exact Work.BoseBox.fsXp_nonneg (le_of_lt (mul_pos hμpos (pow_pos hav 3)))
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
      have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Ψ := by
        rw [Work.BoseFixB1S.boxFlatCount]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hSle : Work.BoseFixB1S.boxFlatCount V ℓ A Ψ ≤ (N : ℝ) + 1 := by
        have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := N + 1) hℓpos' hVpos' hAmeas hAsub
          hAvol hΨcd.continuous
        rw [hnormΨ, mul_one] at hh
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      have hQ0 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
        rw [Work.UBBInputs8.cnPlusBoxInd]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hVle : V ≤ (ℓ * dd) ^ 3 := by
        rw [hVdef, hℓdef, hddef]; exact hVcube
      have hc6 : c ^ 6 = ((_root_.BoseGases.a v) ^ 6)⁻¹ * Xp ^ 936 := by
        have h3 : c ^ 3 = ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 468 := by
          have h := Work.BoseFixB1S.sbCut_cube_eq (μ := μ) (α := _root_.BoseGases.a v) hav hμpos
          rw [← hcdef, ← hXpdef] at h
          exact h
        calc c ^ 6 = (c ^ 3) ^ 2 := by ring
          _ = (((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 468) ^ 2 := by rw [h3]
          _ = ((_root_.BoseGases.a v) ^ 6)⁻¹ * Xp ^ 936 := by
              rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul]
      have hXwle : Xw ≤ κ ^ 2 * V := by
        show (∫ z : E3, (Submission.BoseGases.chiSmallB Mv ℓ dd u z) ^ 2)
            ≤ (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
              * Work.SmallBoxSliding.boxMass ℓ dd u
        exact Work.BoseFixB1S.chiMass_le_const_mul_boxMass hMv1 hℓpos' hdpos' u
      have hVcval : (ℓ * dd) ^ 3 * Xp ^ 471 = (_root_.BoseGases.a v) ^ 3 := by
        have hds := Work.BoseFixB1.d_mul_sideAt_eq (A := _root_.BoseGases.a v) (μ := μ) hav hμpos
        have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
        have hprod : ℓ * dd
            = _root_.BoseGases.a v * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := by
          calc ℓ * dd = Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ := by rw [hℓdef, hddef]
            _ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := rfl
            _ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by rw [mul_comm]
            _ = _root_.BoseGases.a v * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := hds
        have hXpP : Xp ^ 471 = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 471 := by
          show (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1) ^ 471
              = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 471
          rw [Work.BoseBox.fsXp_pow ht0.le 1 471]
          norm_num
        have hzero : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 0 = 1 := by
          simp only [Work.BoseBox.fsXp]
          rw [zero_div, Real.rpow_zero]
        have hkey : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157)) ^ 3
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 471 = 1 := by
          rw [Work.BoseBox.fsXp_pow ht0.le (-157) 3, Work.BoseBox.fsXp_mul ht0]
          convert hzero using 2
          norm_num
        rw [hprod, hXpP, mul_pow,
          show (_root_.BoseGases.a v) ^ 3 * (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157)) ^ 3
              * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 471
            = (_root_.BoseGases.a v) ^ 3
              * ((Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157)) ^ 3
                  * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 471) by ring,
          hkey, mul_one]
      have hVX : V * Xp ^ 471 ≤ (_root_.BoseGases.a v) ^ 3 := by
        have hXppos : 0 < Xp ^ 471 := by
          rw [hXpdef]
          exact pow_pos (Work.BoseBox.fsXp_pos (mul_pos hμpos (pow_pos hav 3))) 471
        calc V * Xp ^ 471 ≤ (ℓ * dd) ^ 3 * Xp ^ 471 :=
              mul_le_mul_of_nonneg_right hVle hXppos.le
          _ = (_root_.BoseGases.a v) ^ 3 := hVcval
      have harith := slidingChainArithB (N := N) (av := _root_.BoseGases.a v)
        (V := V) (c := c) (Xp := Xp) (Xw := Xw)
        (S := Work.BoseFixB1S.boxFlatCount V ℓ A Ψ) (K := Ks) (Ks := Ks) (PM := PM) (κ := κ)
        (D := D) (η := η) (C := C) (μ := μ) (Θ := Θ)
        (Q := Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ)
        (by omega) hav hVpos' hDpos hμpos hcpos hKs0 hXw0 hXp0 hXp1 hκ0 hQ0 hSle hS0 hΘdef hc6
        hVX hXwle hXpPow hKsPM hηK hη0 hCκ hCint
      -- ### the chain's conclusion, transported to the normalised state
      have hA2Ψ : Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.BoseFixB1.boxA2 ℓ V A (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ := by
        show Work.BoseFixB1.boxA2 ℓ V A
            (Submission.BoseGases.wSmall1Pair h Mv ℓ dd u) Ψ = _
        rw [Work.BoseFixB1B.pairRung.wSmall1Pair_kernel h Mv ℓ dd u]
        rfl
      have hchain' : Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          ≥ - (Work.BoseFixB1S.boxFlatCount V ℓ A Ψ) * Xw
                * (c ^ 3 * Ks * (_root_.BoseGases.a v) / (3 * Real.pi ^ 2 * V)
                    + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
              - Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
              - (4 * Ks * κ ^ 2) * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
        rw [← hA2Ψ] at hchain
        convert hchain using 1 <;> ring
      have harith' : 0 ≤ (1 / 2) * (1 + η) * D
            * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
          - (Work.BoseFixB1S.boxFlatCount V ℓ A Ψ) * Xw
              * (c ^ 3 * Ks * (_root_.BoseGases.a v) / (3 * Real.pi ^ 2 * V)
                  + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ
          - (4 * Ks * κ ^ 2) * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ
          + C * (_root_.BoseGases.a v) * μ := by
        convert harith using 1 <;> ring
      have htargetΨ : 0 ≤ (1 / 2) * (1 + η) * D
            * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
          + Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
          + Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ
          + C * (_root_.BoseGases.a v) * μ := by
        linarith [hchain', harith']
      -- ### scaling back to `Φ`
      have hscSpec : Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := by
        show Work.UBBInputs8.tBwordKinInd ℓ A V χ c (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
        rw [hΦeq]
        exact Work.BoseFixB1.tBwordKinInd_mul ℓ V χ c t Ψ
      have hscA2 : Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1.bA2_mul v h μ t Ψ u
      have hscQ : Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1.bQ_mul v μ t Ψ u
      have hscI : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) = t ^ 2 := by
        rw [hΦeq, Work.BoseFixB1.bI_mul, hbIval, mul_one]
      have hQeq : Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := rfl
      have hchiM : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u = Xw := by
        show (∫ z : E3, (Submission.BoseGases.chiSmallB Mv ℓ dd u z) ^ 2) = Xw
        rw [hXwdef]
      have hgoal_eq : (1 / 2 : ℝ) * (1 + η) * Submission.BoseGases.g0w0Mass (v := v) h
            * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) ℓ dd u
          + Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * (μ + ((N : ℝ) + 1) / V)
              * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ)
          = Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            * ((1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
              + Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
              + Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
              + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ
              + C * (_root_.BoseGases.a v) * μ) := by
        rw [hscSpec, hscA2, hscQ, hscI, hchiM, hQeq, hDdef]
        ring
      erw [hgoal_eq]
      exact mul_nonneg hIpos.le htargetΨ

end Work.BoseFixB1B
