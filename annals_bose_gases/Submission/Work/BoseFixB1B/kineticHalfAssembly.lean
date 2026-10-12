import ChallengeDeps
import Submission.Work.BoseFixB1.KH.gap_pairing
import Submission.Work.BoseFixB1.KH.kineticHalf_le_mainWord
import Submission.Work.BoseFixB1.oneBodyKineticHalfAux
import Submission.Work.BoseFixB1.slidingBC_holds
import Submission.Work.BoseFixB1B.corrInputWire
import Submission.Work.BoseFixB1S.integrableHalvesB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.kineticHalfAssembly` — the last mile of FS `eq:BSsliding2`'s
kinetic half

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## What this file is

The a-priori chapter's single open analytic input is `Work.BoseFixB1.SlidingB` (FS
`eq:BSsliding2`, Bratteli--Solovej Thm 3.10).  The chapter reduces it
(`slidingB_of_kineticHalf`, proved) to `KineticHalf`, and the kinetic half is reduced
(`KineticHalfHolds`, `kineticHalf_of_oneBody`, `KH.kineticHalf_le_mainWord`,
`KH.gap_pairing`, all proved) to the one *residual* `Work.BoseFixB1S.CorrInput v` — the
intersection/anchored mean-mismatch step (the `(E2)`+`(E3)` step of
`BoseFixB1S/FINDING_unprojected_route_B.md`).

The single missing link between those proved pieces and `SlidingB` is **bookkeeping**: the
one-body accounting of `KH/ASSEMBLY.md` §2, which combines

* the definitional split of `sbKin` at `N = 1` (`integral_sbKin_split`, with the *marginal*
  integrability of both halves from `BoseFixB1S.integrable_halves_general`),
* the sliding gap pairing (`KH.gap_pairing`, FS `eq:appTB` against the anchored Neumann term),
  whose constant `tbGapCoeff (ℓd) ε_T ·(1+π⁻²) = ½ε_T(dℓ)⁻²` is exactly `neuWord`'s coefficient,
* the sliding spectral half (`KH.kineticHalf_le_mainWord`, stated at FS's parameters, from
  `CorrInput` + the two proved symbol inputs),
* the anchored bookkeeping of `oneBodyKineticHalfAux` (`cnPlus_one_eq`, `gapWord_zero`,
  `neuWord_zero`), `kinFormBOne_eq_fsT` and `momWord_nonneg`.

The conclusion is `KineticHalf` and then `SlidingB`, **given `CorrInput v`**.

## The statements

* `oneBodyKineticHalf_of_inputs` — the one-body inequality (the `h1` of
  `kineticHalf_of_oneBody`) from `CorrInput`, `UnprojInput`, `MixInput`;
* `kineticHalf_of_inputs` — `Work.BoseFixB1.KineticHalf v h` from the same three inputs
  (the marginal-integrability conjunct is the proved `integrable_sbKin_all`);
* `slidingB_of_inputs` — **FS `eq:BSsliding2`** (`Work.BoseFixB1.SlidingB v h`) from the same
  three inputs, so that once `Work.BoseFixB1S.CorrInput v` is proved, `slidingB_holds` — and
  hence the a-priori inequalities `aprioriHLambdaIneq_holds`, and hence the count bound
  `Work.BoseFixB1B.lowCountBound` — are immediate from this file.

`CorrInput` itself is decomposed by the proved `Work.BoseFixB1S.cruxCorrB1_of_pieces` into the
six pieces `CutWords`, `MeanSq`, `Marginal`, `Arith`, `ChiL2`, `PlanchMarg`; of these,
`CutWords` (`BoseFixB1S/corrCutWords.lean`), `ChiL2` (`corrChiScaleL2.lean`) and `PlanchMarg`
(`corrPlanchMarg.lean`) are proved, and `Arith` is proved in
`Submission/Work/BoseFixB1B/corrArithHold.lean` (this author).  Only `MeanSq` and `Marginal`
remain.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The one-body inequality from the three crux inputs -/

/-- **The one-body kinetic inequality** (the `h1` of `Work.BoseFixB1.kineticHalf_of_oneBody`),
from the three inputs of `Work.BoseFixB1S.kineticCruxParsed_of_inputs`: the mean-mismatch
residual `CorrInput`, the unprojected family form `UnprojInput` and the two-cut symbol
comparison `MixInput`.

LHS = `(b/2ℓ²)·cnPlus ℓ φ + ∫_u sbKin v μ P.M u φ`, RHS = `kinFormB 1 ℓ P.d P.s P.eT P.b φ`.
Everything is the accounting of `KH/ASSEMBLY.md` §2. -/
theorem oneBodyKineticHalf_of_inputs {v : E3 → ℝ}
    (hcorr : Work.BoseFixB1S.CorrInput v) (hunproj : Work.BoseFixB1S.UnprojInput)
    (hmix : Work.BoseFixB1S.MixInput v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2)
            * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ
          + (∫ u : E3,
              Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ := by
  obtain ⟨ε₁, hε₁, hKIN⟩ :=
    Work.BoseFixB1.KH.kineticHalf_le_mainWord_of_inputs hcorr hunproj hmix
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro μ hAdm φ hφ
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  -- positivity at FS's parameters
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have heT0' : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hb0' : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b :=
    le_of_lt (Work.BoseFixB1.paramsAt_b_pos μ (_root_.BoseGases.a v))
  -- abbreviations
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓd
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hdd
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsd
  set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTd
  set b : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b with hbd
  set cc : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hccd
  set ψ : E3 → ℝ := Work.BSKinetic.slotFun1 φ with hψd
  have hℓpos' : 0 < ℓ := hℓpos
  have hdpos' : 0 < d := hdpos
  have heT0 : 0 ≤ eT := heT0'
  have hb0 : 0 ≤ b := hb0'
  have hbval : b = Work.BoseBox.bValue := by
    rw [hbd]; exact Work.BoseFixB1.paramsAt_b_eq μ (_root_.BoseGases.a v)
  have hψc : ContDiff ℝ (⊤ : ENat) ψ := by
    rw [hψd]; exact hφ.comp (by fun_prop)
  have hφψ : (fun x : Submission.BoseGases.X 1 => ψ (x 0)) = φ := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext j; fin_cases j; rfl
    rw [hψd, Work.BSKinetic.slotFun1, hx]
  -- ## the split of `∫_u sbKin`
  obtain ⟨hIgap, hIdiag⟩ :=
    Work.BoseFixB1S.integrable_halves_general (ℓ := ℓ) (d := d) (ε := eT) (c := cc)
      hℓpos' hdpos' heT0 hφ
  have hIkin : MeasureTheory.Integrable (fun u : E3 =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) cc φ) := hIdiag
  have hsplit : (∫ u : E3,
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u φ)
      = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        + ∫ u : E3, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) cc φ := by
    have h := Work.BoseFixB1.integral_sbKin_split (v := v) μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M φ
      (by simpa only [← hℓd, ← hdd, ← heTd, ← hccd] using hIgap)
      (by simpa only [← hℓd, ← hdd, ← hccd] using hIkin)
    simp only [← hℓd, ← hdd, ← heTd, ← hccd] at h
    exact h
  -- ## the sliding gap half
  have hgap_raw := Work.BoseFixB1.KH.gap_pairing hℓpos' hdpos' ψ hψc
  have hgapeq : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT * (1 + (Real.pi ^ 2)⁻¹)
      = (1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (d * ℓ) ^ (-2 : ℤ) = ((ℓ * d) ^ 2)⁻¹ by
      rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
      congr 1
      ring]
    rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
    have hpi : (1 + (Real.pi ^ 2)⁻¹) ≠ 0 := by positivity
    field_simp
  have hgap1 : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
        (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ)
      ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
    have h1 : (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        ≤ (1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ) := by
      rw [← hφψ]
      exact hgap_raw
    have h2 : Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          ((1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ))
        = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
      rw [← mul_assoc, hgapeq, Work.BoseFixB1.neuWord_zero]
      rfl
    calc Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
          (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) φ)
        ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
            ((1 + (Real.pi ^ 2)⁻¹) *
              Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ)) :=
            mul_le_mul_of_nonneg_left h1 (Work.SmallBoxTBWord.tbGapCoeff_nonneg heT0)
      _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := h2
  -- ## the sliding spectral half
  have hkin : (∫ u : E3, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) cc φ)
      ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
        + (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ φ := by
    have hK := hKIN μ hAdm₁ φ hφ
    simp only [← hℓd, ← hdd, ← hsd, ← heTd, ← hccd, ← hψd] at hK
    exact hK
  -- ## the anchored bookkeeping
  have hfsT : Work.BoseKinLoc.kinFormB 1 ℓ d s eT b φ
      = Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ := by
    rw [Work.BoseFixB1.kinHalf_kinFormBOne hℓpos' φ hφ, ← hψd]
  have hfsTdef : Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
      = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + Work.BoseKinLoc.gapWord ℓ b 0 ψ
        + Work.BoseKinLoc.momWord ℓ d eT b 0 ψ + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := rfl
  have hcn : Submission.BoseGases.cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 := by
    rw [Work.BoseFixB1.cnPlus_one_eq hℓpos' φ hφ, ← hψd]
  have hgapW : Work.BoseKinLoc.gapWord ℓ b 0 ψ
      = b * ℓ ^ (-2 : ℤ) * ∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 :=
    Work.BoseFixB1.gapWord_zero ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d eT b 0 ψ :=
    Work.BoseFixB1.momWord_nonneg hb0 heT0 0 ψ
  have hbsum : Work.BoseBox.bValue / (2 * ℓ ^ 2) + Work.BoseBox.bValue / (2 * ℓ ^ 2)
      = b * ℓ ^ (-2 : ℤ) := by
    rw [hbval, show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos'
    field_simp
    ring
  have hbval2 : b / (2 * ℓ ^ 2) = Work.BoseBox.bValue / (2 * ℓ ^ 2) := by rw [hbval]
  -- ## assemble
  rw [hfsT, hfsTdef, hsplit, hcn]
  rw [hcn] at hkin
  calc b / (2 * ℓ ^ 2) *
        (∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
        + (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
              (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) φ)
            + ∫ u : E3, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) cc φ)
      ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
        + b * ℓ ^ (-2 : ℤ) *
            (∫ z in Submission.BoseGases.acube ℓ,
              (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
        + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
        rw [hbval2]
        calc Work.BoseBox.bValue / (2 * ℓ ^ 2) *
              (∫ z in Submission.BoseGases.acube ℓ,
                (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
              + (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) eT *
                    (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                      (Work.SmallBoxSliding.boxMass ℓ d u) φ)
                  + ∫ u : E3, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) cc φ)
            ≤ Work.BoseBox.bValue / (2 * ℓ ^ 2) *
                (∫ z in Submission.BoseGases.acube ℓ,
                  (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
              + (Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
                  + (Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
                      + Work.BoseBox.bValue / (2 * ℓ ^ 2) *
                          (∫ z in Submission.BoseGases.acube ℓ,
                            (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ,
                              ψ z') ^ 2))) := by
              linarith [hgap1, hkin]
          _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
                + (Work.BoseBox.bValue / (2 * ℓ ^ 2) + Work.BoseBox.bValue / (2 * ℓ ^ 2)) *
                    (∫ z in Submission.BoseGases.acube ℓ,
                      (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
                + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by ring
          _ = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
                + b * ℓ ^ (-2 : ℤ) *
                    (∫ z in Submission.BoseGases.acube ℓ,
                      (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
                + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by rw [hbsum]
      _ ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + Work.BoseKinLoc.gapWord ℓ b 0 ψ
        + Work.BoseKinLoc.momWord ℓ d eT b 0 ψ + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
        rw [hgapW]
        linarith [hmom]

/-! ## 2. `KineticHalf` from the three crux inputs -/

/-- **FS `eq:BSsliding2`'s kinetic half** (`Work.BoseFixB1.KineticHalf v h`) from the three inputs
of `Work.BoseFixB1S.kineticCruxParsed_of_inputs`.  The `u`-marginal integrability conjunct is
the proved `Work.BoseFixB1.integrable_sbKin_all`. -/
theorem kineticHalf_of_inputs {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hcorr : Work.BoseFixB1S.CorrInput v) (hunproj : Work.BoseFixB1S.UnprojInput)
    (hmix : Work.BoseFixB1S.MixInput v) : Work.BoseFixB1.KineticHalf v h :=
  Work.BoseFixB1.kineticHalf_of_oneBody h
    (oneBodyKineticHalf_of_inputs hcorr hunproj hmix)
    (Work.BoseFixB1.integrable_sbKin_all h)

/-! ## 3. FS `eq:BSsliding2` from the three crux inputs -/

/-- **FS `eq:BSsliding2`** (Bratteli--Solovej Thm 3.10 at FS's parameters, the a-priori chapter's
single open analytic input) from the three inputs of
`Work.BoseFixB1S.kineticCruxParsed_of_inputs`.  The potential half is the proved
`Work.BoseFixB1.slidingB_of_kineticHalf` / `potentialHalf_holds`. -/
theorem slidingB_of_inputs {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hcorr : Work.BoseFixB1S.CorrInput v) (hunproj : Work.BoseFixB1S.UnprojInput)
    (hmix : Work.BoseFixB1S.MixInput v) : Work.BoseFixB1.SlidingB v h :=
  Work.BoseFixB1.slidingB_of_kineticHalf hv1 hvrad hR hv_supp hav
    (kineticHalf_of_inputs h hcorr hunproj hmix)

/-! ## 4. FS `eq:BSsliding2` from `CorrInput` -/

/-- **FS `eq:BSsliding2`** (`Work.BoseFixB1.SlidingB`, the a-priori chapter's single open
analytic input) from the *two* remaining pieces `MeanSq` and `Marginal` of the intersection-mean
correction (`corrInput_of_pieces`, in `corrInputPieces.lean`). -/
theorem slidingB_of_meanSq_marginal {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hMean : Work.BoseFixB1S.MeanSq v) (hMarg : Work.BoseFixB1S.Marginal v) :
    Work.BoseFixB1.SlidingB v h :=
  slidingB_of_inputs h hv1 hvrad hR hv_supp hav (corrInput_of_pieces h hMean hMarg)
    Work.BoseFixB1.KH.unprojInputB1 (Work.BoseFixB1.KH.mixInputB1 (v := v))

/-- **FS `eq:BSsliding2`** (Bratteli--Solovej Thm 3.10 at FS's parameters) — **PROVED**.

This is `Work.BoseFixB1.SlidingB v h`, the a-priori chapter's single open analytic input:
its potential half is `Work.BoseFixB1.slidingB_of_kineticHalf`/`potentialHalf_holds`, its kinetic
half is `kineticHalf_of_inputs`, and the whole intersection-mean correction `CorrInput v` that
the kinetic half rests on is `Work.BoseFixB1B.corrInput_holds` (proved in `corrInputWire.lean`).
So `slidingB_holds`'s `sorry` can be filled by
`Work.BoseFixB1B.slidingB_holds_from_assembly h hv1 hvrad hR hv_supp hav`. -/
theorem slidingB_holds_from_assembly {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.SlidingB v h :=
  slidingB_of_inputs h hv1 hvrad hR hv_supp hav (Work.BoseFixB1B.corrInput_holds h)
    Work.BoseFixB1.KH.unprojInputB1 (Work.BoseFixB1.KH.mixInputB1 (v := v))

end Work.BoseFixB1B
