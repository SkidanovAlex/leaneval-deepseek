import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1.Core.meanMismatch_le
import Submission.Work.BoseFixB1.Core.pnorm_payment
import Submission.Work.BoseFixB1.Core.spectral_chain
import Submission.Work.BoseFixB1.kinFormBOne_eq_fsT
import Submission.Work.BoseFixB1.momWord_nonneg
import Submission.Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac
import Submission.Work.BoseFixB1P.gapWord_zero_slotFun1_eq
import Submission.Work.BoseFixB1P.integral_tBwordKinInd_eq_bsW
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Elementary identifications -/

/-- The `p`-space spelling of the unprojected one-body family form:
`bsOneBodyUnproj a F u ψ = (2π)⁻³·bsW F (bsWin a u · ψ)`. -/
lemma bsOneBodyUnproj_eq_bsW_bsWin (a : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsOneBodyUnproj a F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F
          (fun z : ℝ³ => Work.BSKinetic.bsWin a u z * ψ z) := by
  have hff : (fun z : ℝ³ => ((Work.BSKinetic.bsWin a u z * ψ z : ℝ) : ℂ))
      = fun z : ℝ³ => (Work.BSKinetic.bsWin a u z : ℂ) * (ψ z : ℂ) := by
    funext z
    exact Complex.ofReal_mul _ _
  simp only [Work.BSKinetic.bsOneBodyUnproj, Work.BSKinetic.Decomp.bsW,
    Work.BSKinetic.Decomp.bsPsi, hff]

/-- `χ_{B(u)}·h = bsWin (ℓd)u·(χ_ℓ·h)`: the product window `χ_{B(u)} = χ_ℓ·bsWin (ℓd)u`. -/
lemma chiB_mul_eq_bsWin_mul (ℓ d : ℝ) (u : ℝ³) (h : ℝ³ → ℝ) :
    (fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * h z)
      = fun z : ℝ³ => Work.BSKinetic.bsWin (ℓ * d) u z *
          (Submission.BoseGases.chiScale ℓ z * h z) := by
  funext z
  simp only [Submission.BoseGases.chiB, Work.BSKinetic.bsWin]
  ring

/-- **The unprojected family form of the anchored-mean-free windowed state.**  With
`ψ₀ = χ_ℓ(ψ − M)`,

    `bsFamilyFormUnproj (d·ℓ) F ψ₀ = ∫_u (2π)⁻³·bsW F (χ_{B(u)}·(ψ − M))`. -/
lemma famUnproj_chiB (ℓ d : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) (M : ℝ) :
    Work.BSKinetic.bsFamilyFormUnproj (d * ℓ) F
        (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ z * (ψ z - M))
      = ∫ u : ℝ³, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F
          (fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * (ψ z - M)) := by
  have hcomm : d * ℓ = ℓ * d := mul_comm d ℓ
  have hfun : ∀ u : ℝ³, (fun z : ℝ³ => Work.BSKinetic.bsWin (d * ℓ) u z *
        (Submission.BoseGases.chiScale ℓ z * (ψ z - M)))
      = fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * (ψ z - M) := by
    intro u
    funext z
    simp only [Submission.BoseGases.chiB, Work.BSKinetic.bsWin, hcomm]
    ring
  rw [Work.BSKinetic.bsFamilyFormUnproj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [bsOneBodyUnproj_eq_bsW_bsWin (d * ℓ) F u
    (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ z * (ψ z - M)), hfun u]

/-- **`cnPlus` at one particle is the anchored box mean-square.**  With `ψ = slotFun1 φ`,

    `cnPlus ℓ φ = ∫_{acube ℓ}(ψ − ℓ⁻³∫_{acube ℓ}ψ)²`.

Derived from the proved `gapWord_zero_slotFun1_eq` by cancelling the nonzero factor
`b·ℓ⁻²` and unfolding `gapBare = ∫_{acube ℓ}(Qfree ℓ 0 ψ)²`. -/
lemma cnPlus_one_eq_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (φ : X 1 → ℝ) :
    cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ, (Work.BSKinetic.slotFun1 φ z
          - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ,
              Work.BSKinetic.slotFun1 φ z') ^ 2 := by
  have h := Work.BoseFixB1P.gapWord_zero_slotFun1_eq ℓ (1 / 16) φ
  have h2 : Work.BoseKinLoc.gapWord ℓ (1 / 16) 0 (Work.BSKinetic.slotFun1 φ)
      = (1 / 16) * ℓ ^ (-2 : ℤ)
          * Work.BoseKinLoc.gapBare ℓ 0 (Work.BSKinetic.slotFun1 φ) := rfl
  rw [h2] at h
  have hcoef : (1 / 16 : ℝ) * ℓ ^ (-2 : ℤ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    rw [zpow_neg, zpow_two]
    exact inv_ne_zero (mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hℓ))
  have hcancel : Work.BoseKinLoc.gapBare ℓ 0 (Work.BSKinetic.slotFun1 φ) = cnPlus ℓ φ :=
    mul_left_cancel₀ hcoef h
  rw [← hcancel]
  simp only [Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ,
    Work.BoseFixB1P.lamBox_zero, Work.BoseFixB1P.bsMean_zero_eq]

/-- `bsQ ℓ 0 ψ = ψ − ℓ⁻³∫_{acube ℓ}ψ`, the anchored big-box mean-free projection. -/
lemma bsQ_zero_eq (ℓ : ℝ) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsQ ℓ 0 ψ
      = fun z : ℝ³ => ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z' := by
  funext z
  simp only [Work.BSKinetic.bsQ, Work.BoseFixB1P.bsMean_zero_eq]

/-- `(2π)⁻³ ≤ 1`. -/
lemma twoPi_inv_cube_le_one : ((2 * Real.pi) ^ 3 : ℝ)⁻¹ ≤ 1 := by
  have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h3 : (1 : ℝ) ≤ (2 * Real.pi) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (2 * Real.pi) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  exact inv_le_one_of_one_le₀ h3

/-- `tbGapCoeff (ℓd) ε_T·(1+π⁻²)` is FS's `½ε_T(dℓ)⁻²`, the coefficient of `neuWord`. -/
lemma tbGapCoeff_mul_pi {ℓ d ε : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε * (1 + (Real.pi ^ 2)⁻¹)
      = (1 / 2) * ε * (d * ℓ) ^ (-2 : ℤ) := by
  have hpi : (1 + (Real.pi ^ 2)⁻¹) ≠ 0 := by positivity
  have hld : (ℓ * d) ≠ 0 := mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)
  have hsq : (ℓ * d) ^ 2 = (d * ℓ) ^ 2 := by ring
  rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor, hsq, zpow_neg, zpow_two]
  field_simp

/-- `tbGapCoeff (ℓd) ε_T ≥ 0` for `ε_T ≥ 0`. -/
lemma tbGapCoeff_nonneg {ℓ d ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε := by
  rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (by positivity))
    (inv_nonneg.mpr (sq_nonneg _))

/-! ## 1. The theorem -/

/-- **The `N = 1` kinetic inequality** — FS `eq:BSsliding2`'s kinetic core at FS's parameters,
verbatim the statement of `Work.BoseFixB1.oneBodyKineticHalf`. -/
theorem oneBodyKineticHalf_core {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2)
            * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ
          + (∫ u : EuclideanSpace ℝ (Fin 3),
              sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ := by
  by_cases hav : 0 < _root_.BoseGases.a v
  · obtain ⟨εM, hεM, hM⟩ := Work.BoseFixB1.Core.meanMismatch_le (v := v) h
    obtain ⟨εS, hεS, hS⟩ := Work.BoseFixB1.Core.spectral_chain (v := v) h hav
    obtain ⟨εP, hεP, hP⟩ := Work.BoseFixB1.Core.pnorm_payment (v := v) h hav
    refine ⟨min εM (min εS εP), lt_min hεM (lt_min hεS hεP), ?_⟩
    intro μ hAdm φ hφ
    have hadmM : Adm v εM μ := Adm.mono hAdm (min_le_left _ _)
    have hadmS : Adm v εS μ := Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    have hadmP : Adm v εP μ := Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
    have hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
    have hd0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
    have hs0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := adm_s_pos hAdm
    have hb0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b := adm_b_nonneg hAdm
    have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
      (adm_eT_bounds hAdm).1
    have hψc : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.slotFun1 φ) :=
      hφ.comp (by fun_prop)
    -- abbreviations
    set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓd
    set dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hdd
    set ss : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hss
    set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTd
    set bb : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b with hbb
    set cc : ℝ := sbCut μ (_root_.BoseGases.a v) with hccd
    set ψ : ℝ³ → ℝ := Work.BSKinetic.slotFun1 φ with hψd
    set E : ℝ := ∫ z in Submission.BoseGases.acube ℓ,
        (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 with hE
    have hℓ : 0 < ℓ := by rw [hℓd]; exact hℓ0
    have hd : 0 < dd := by rw [hdd]; exact hd0
    have hs : 0 < ss := by rw [hss]; exact hs0
    have hb : 0 ≤ bb := by rw [hbb]; exact hb0
    have heT : 0 ≤ eT := by rw [heTd]; exact heT0
    have hψ : ContDiff ℝ (⊤ : ENat) ψ := by rw [hψd]; exact hψc
    have hcc_pos : 0 < cc := by
      rw [hccd, Work.BoseFixB1.sbCut]
      exact inv_pos.mpr (mul_pos (mul_pos hd hs) hℓ)
    have hE0 : 0 ≤ E := by
      rw [hE]
      exact MeasureTheory.integral_nonneg fun z => sq_nonneg _
    -- the goal in abbreviations
    rw [Work.BoseFixB1.kinFormBOne_eq_fsT (ℓ := ℓ) hℓ φ, ← hψd]
    simp only [Work.BoseKinLoc.fsT, Work.BoseFixB1.sbKin, Work.UBBInputs8.tBwordBInd,
      ← hℓd, ← hdd, ← heTd, ← hccd]
    -- integrability of the two halves of `sbKin`
    have hIntSum : Integrable (fun u : ℝ³ => Work.UBBInputs8.tBwordInd ℓ
        (Submission.BoseGases.dlBox ℓ dd u) (Work.SmallBoxSliding.boxMass ℓ dd u)
        (Submission.BoseGases.chiB ℓ dd u) (ℓ * dd) eT cc φ) :=
      integrable_tBwordBInd (ℓ := ℓ) (d := dd) (ε := eT) (c := cc) hℓ hd (N := 1) hφ
    have hg_eq : ∀ u : ℝ³, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
        (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
            (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, ψ z')) :=
      fun u => Work.BoseFixB1P.tBwordKinInd_one_eq_bsW hℓ hd φ u
    have hIntG : Integrable (fun u : ℝ³ =>
        Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
          (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ) := by
      have h' := (Work.BoseFixB1P.integral_tBwordKinInd_eq_bsW (ℓ := ℓ) (d := dd) (c := cc)
        hℓ hd hcc_pos.le φ hφ).1
      exact h'.congr (Filter.Eventually.of_forall fun u => (hg_eq u).symm)
    have hIntF : Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
          (Work.SmallBoxSliding.boxMass ℓ dd u) φ) := by
      refine (hIntSum.sub hIntG).congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [Pi.sub_apply, Work.UBBInputs8.tBwordInd]
      ring
    have hsplit : (∫ u : ℝ³, Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
          (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) (ℓ * dd) eT cc φ)
        = (∫ u : ℝ³, Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
              Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
                (Work.SmallBoxSliding.boxMass ℓ dd u) φ)
          + ∫ u : ℝ³, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
              (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ := by
      have hfun : (fun u : ℝ³ => Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
            (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u)
            (ℓ * dd) eT cc φ)
          = fun u : ℝ³ => Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
              Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
                (Work.SmallBoxSliding.boxMass ℓ dd u) φ
              + Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
                  (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u)
                  cc φ := by
        funext u
        simp only [Work.UBBInputs8.tBwordInd]
      rw [hfun, MeasureTheory.integral_add hIntF hIntG]
    -- (L1)/(L2): the gap line
    have hL2 : (∫ u : ℝ³, Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
          Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
            (Work.SmallBoxSliding.boxMass ℓ dd u) φ)
        ≤ Work.BoseKinLoc.neuWord ℓ dd eT 0 ψ := by
      have hcb := Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac (ℓ := ℓ) (d := dd)
        hℓ hd ψ hψ
      have hφeq : (fun x : Submission.BoseGases.X 1 => ψ (x 0)) = φ := by
        funext x
        simp only [hψd, Work.BSKinetic.slotFun1]
        congr 1
        funext j
        fin_cases j
        rfl
      rw [hφeq] at hcb
      calc (∫ u : ℝ³, Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
            Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
              (Work.SmallBoxSliding.boxMass ℓ dd u) φ)
          = Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
              (∫ u : ℝ³, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
                (Work.SmallBoxSliding.boxMass ℓ dd u) φ) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * dd) eT *
              ((1 + (Real.pi ^ 2)⁻¹) * Work.BoseKinLoc.neuFrac ℓ ((dd * ℓ) ^ (-2 : ℤ)) 0
                (Work.BoseKinLoc.Qfree ℓ 0 ψ)) :=
            mul_le_mul_of_nonneg_left hcb (tbGapCoeff_nonneg heT)
        _ = Work.BoseKinLoc.neuWord ℓ dd eT 0 ψ := by
            rw [Work.BoseKinLoc.neuWord, ← tbGapCoeff_mul_pi hℓ hd]
            ring
    -- the `cnPlus`/`gapWord` identifications
    have hcn : cnPlus ℓ φ = E := by
      rw [cnPlus_one_eq_acube hℓ φ, ← hψd]
    have hgap : Work.BoseKinLoc.gapWord ℓ bb 0 ψ = bb * ℓ ^ (-2 : ℤ) * E := by
      have hgb : Work.BoseKinLoc.gapBare ℓ 0 ψ = E := by
        rw [hE]
        simp only [Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ,
          Work.BoseFixB1P.lamBox_zero, Work.BoseFixB1P.bsMean_zero_eq]
      rw [show Work.BoseKinLoc.gapWord ℓ bb 0 ψ
          = bb * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapBare ℓ 0 ψ from rfl, hgb]
    have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ dd eT bb 0 ψ :=
      momWord_nonneg hb heT 0 ψ
    -- the crux, the spectral chain and the payment, in abbreviations
    have hM' := hM μ hadmM ψ hψ
    rw [← hℓd, ← hdd, ← hbb, ← hccd] at hM'
    have hdivℓ : (1 : ℝ) / ℓ ^ 3 = (ℓ ^ 3)⁻¹ := one_div _
    simp only [hdivℓ] at hM'
    rw [← hE] at hM'
    have hP' := hP μ hadmP ψ hψ
    rw [← hℓd, ← hdd, ← hss, ← hbb] at hP'
    simp only [hdivℓ] at hP'
    rw [← hE] at hP'
    have hS' := hS μ hadmS ψ hψ
    rw [← hℓd, ← hdd, ← hss, ← heTd, ← hccd] at hS'
    simp only [bsQ_zero_eq] at hS'
    -- assemble
    have hfp : Work.BoseKinLoc.momWord ℓ dd eT bb 0 ψ
        + (bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E
        = Work.BoseKinLoc.momWord ℓ dd eT bb 0 ψ
          + ((bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E) := by ring
    have hKin : (∫ u : ℝ³, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
          (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ)
        ≤ Work.BoseKinLoc.mainWord ℓ dd ss eT 0 ψ
          + (bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E := by
      have hstep1 : (∫ u : ℝ³,
            Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
              (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ)
          = ∫ u : ℝ³, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff cc)
              (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
                  ∫ z' in Submission.BoseGases.dlBox ℓ dd u, ψ z')) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hg_eq)
      have hstep2 : (∫ u : ℝ³, ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff cc)
              (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
                  ∫ z' in Submission.BoseGases.dlBox ℓ dd u, ψ z')))
          = ((2 * Real.pi) ^ 3)⁻¹ * ∫ u : ℝ³, Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff cc)
              (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
                  ∫ z' in Submission.BoseGases.dlBox ℓ dd u, ψ z')) :=
        MeasureTheory.integral_const_mul _ _
      have hcruxM := mul_le_mul_of_nonneg_left hM' (by positivity : (0:ℝ) ≤ ((2*Real.pi)^3)⁻¹)
      have hring : ((2 * Real.pi) ^ 3)⁻¹ *
            ((∫ u : ℝ³, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
                (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                  (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')))
              + (bb / (8 * ℓ ^ 2)) * E)
          = ((2 * Real.pi) ^ 3)⁻¹ *
              (∫ u : ℝ³, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
                (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                  (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')))
            + ((2 * Real.pi) ^ 3)⁻¹ * ((bb / (8 * ℓ ^ 2)) * E) := by ring
      have hlast : ((2 * Real.pi) ^ 3)⁻¹ * ((bb / (8 * ℓ ^ 2)) * E)
          ≤ (bb / (8 * ℓ ^ 2)) * E := by
        have h1 : 0 ≤ (bb / (8 * ℓ ^ 2)) * E :=
          mul_nonneg (div_nonneg hb (by positivity)) hE0
        have h2 : ((2 * Real.pi) ^ 3)⁻¹ * ((bb / (8 * ℓ ^ 2)) * E)
            ≤ 1 * ((bb / (8 * ℓ ^ 2)) * E) :=
          mul_le_mul_of_nonneg_right twoPi_inv_cube_le_one h1
        simpa using h2
      calc (∫ u : ℝ³, Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ dd u)
              (Work.SmallBoxSliding.boxMass ℓ dd u) (Submission.BoseGases.chiB ℓ dd u) cc φ)
          = ((2 * Real.pi) ^ 3)⁻¹ * ∫ u : ℝ³, Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff cc)
              (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
                  ∫ z' in Submission.BoseGases.dlBox ℓ dd u, ψ z')) := by rw [hstep1, hstep2]
        _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              ((∫ u : ℝ³, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
                  (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                    (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')))
                + (bb / (8 * ℓ ^ 2)) * E) := hcruxM
        _ = ((2 * Real.pi) ^ 3)⁻¹ *
              (∫ u : ℝ³, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
                (fun z : ℝ³ => Submission.BoseGases.chiB ℓ dd u z *
                  (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')))
            + ((2 * Real.pi) ^ 3)⁻¹ * ((bb / (8 * ℓ ^ 2)) * E) := hring
        _ ≤ Work.BSKinetic.bsFamilyFormUnproj (dd * ℓ) (Submission.BoseGases.fsKinCoeff cc)
              (fun z : ℝ³ => Submission.BoseGases.chiScale ℓ z *
                (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z'))
            + (bb / (8 * ℓ ^ 2)) * E := by
            refine add_le_add ?_ hlast
            rw [← MeasureTheory.integral_const_mul]
            exact le_of_eq (famUnproj_chiB ℓ dd (Submission.BoseGases.fsKinCoeff cc) ψ
              ((ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')).symm
        _ ≤ (Work.BoseKinLoc.mainWord ℓ dd ss eT 0 ψ
              + (Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (1 / (2 * ss))) 0
                  / (dd * ℓ) ^ 2) *
                (∫ z : ℝ³, (Submission.BoseGases.chiScale ℓ z) ^ 2 *
                  (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2))
            + (bb / (8 * ℓ ^ 2)) * E := by linarith [hS']
        _ ≤ (Work.BoseKinLoc.mainWord ℓ dd ss eT 0 ψ + (bb / (8 * ℓ ^ 2)) * E)
            + (bb / (8 * ℓ ^ 2)) * E := by
            have hp := hP'
            linarith [hp]
        _ = Work.BoseKinLoc.mainWord ℓ dd ss eT 0 ψ
            + (bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E := by ring
    -- the arithmetic closing the ledger
    have harith : (bb / (2 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E
        ≤ bb * ℓ ^ (-2 : ℤ) * E + Work.BoseKinLoc.momWord ℓ dd eT bb 0 ψ := by
      have hcoef2 : bb / (2 * ℓ ^ 2) + bb / (8 * ℓ ^ 2) + bb / (8 * ℓ ^ 2)
          ≤ bb * ℓ ^ (-2 : ℤ) := by
        have hℓ2 : (0 : ℝ) < ℓ ^ 2 := pow_pos hℓ 2
        have heq : bb / (2 * ℓ ^ 2) + bb / (8 * ℓ ^ 2) + bb / (8 * ℓ ^ 2)
            = (3 * bb / 4) * (ℓ ^ 2)⁻¹ := by
          field_simp
          ring
        calc bb / (2 * ℓ ^ 2) + bb / (8 * ℓ ^ 2) + bb / (8 * ℓ ^ 2)
            = (3 * bb / 4) * (ℓ ^ 2)⁻¹ := heq
          _ ≤ bb * (ℓ ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = bb * ℓ ^ (-2 : ℤ) := by rw [zpow_neg, zpow_two, pow_two]
      calc (bb / (2 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E + (bb / (8 * ℓ ^ 2)) * E
          = (bb / (2 * ℓ ^ 2) + bb / (8 * ℓ ^ 2) + bb / (8 * ℓ ^ 2)) * E := by ring
        _ ≤ (bb * ℓ ^ (-2 : ℤ)) * E := mul_le_mul_of_nonneg_right hcoef2 hE0
        _ = bb * ℓ ^ (-2 : ℤ) * E := by ring
        _ ≤ bb * ℓ ^ (-2 : ℤ) * E + Work.BoseKinLoc.momWord ℓ dd eT bb 0 ψ :=
            le_add_of_nonneg_right hmom
    rw [hcn, hgap, hsplit]
    linarith [hL2, hKin, harith]
  · refine ⟨1, one_pos, fun μ hAdm => ?_⟩
    exact absurd (adm_a_pos hAdm) hav

end Work.BoseFixB1
