import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseFixB1.Defs
import Submission.Work.Measure.ae_measure_section_right_null
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
import Submission.Work.SecondOrder.Main
import Submission.Work.SmallBoxBridge.kinFT_analyticAt
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
import Submission.Work.hlocWire.tBdiagFormInd_smul
import Submission.Work.hlocWire2.bsW_le_of_le_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.oneBodyKineticHalfAux` — the bookkeeping lemmas for `oneBodyKineticHalf`

The assembly of `Work.BoseFixB1.oneBodyKineticHalf` reduces FS `eq:BSsliding2`'s kinetic content
at `N = 1` to a comparison of the two explicit words of FS `eq:DefT` and FS `eq:appTB`.  This
module holds the *definitional* steps of that reduction, each with no analytic content:

* `integral_X0` — the integral over the empty configuration space `X 0` is evaluation at the point
  (the volume of `abox 0 ℓ` is `(ℓ³)⁰ = 1`);
* `cnPlus_one_eq` — at one particle the excited count is the box mean-free mass
  `∫_{acube ℓ}(ψ − M)²`, `ψ = slotFun1 φ`, `M = (ℓ³)⁻¹∫_{acube ℓ}ψ`
  (the `N = 1` case of `Work.BSKinetic.cnPlus_eq_slotSum`);
* `gapWord_zero` — the anchored gap word is `bℓ⁻²` times that mass, so it pays the target's
  `(b/2ℓ²)·cnPlus ℓ φ` with a factor `2` of slack;
* `neuWord_zero` — the anchored Neumann word is `½ε_T(dℓ)⁻²·neuFrac ℓ (dℓ)⁻² 0 (bsQ ℓ 0 ψ)`;
* `mainWord_zero_eq` — the anchored main word is the two-cut mixture
  `(1−ε_T)[·−c₁]₊² + ε_T[·−c₂]₊²` applied to the `p`-Fourier weight of `χ_ℓ(ψ − M)`.

All five are `sorry`-free.
-/

noncomputable section

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `lamBox ℓ 0` is the centred cube `acube ℓ`. -/
lemma lamBox_zero (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- `bsQ ℓ 0 ψ` is `ψ` minus its box mean over `acube ℓ`. -/
lemma bsQ_zero_apply {ℓ : ℝ} (ψ : E3 → ℝ) (x : E3) :
    Work.BSKinetic.bsQ ℓ 0 ψ x
      = ψ x - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, ψ z := by
  simp [Work.BSKinetic.bsQ, Work.BSKinetic.bsMean]

/-- The integral over the empty configuration space `X 0` (restricted to `abox 0 ℓ = univ`,
a probability measure) is evaluation at the unique point. -/
lemma integral_X0 {ℓ : ℝ} (hℓ : 0 < ℓ) (G : Submission.BoseGases.X 0 → ℝ) :
    (∫ r in Submission.BoseGases.abox 0 ℓ, G r) = G 0 := by
  have huniv : Submission.BoseGases.abox 0 ℓ = Set.univ := by
    ext x; simp [Submission.BoseGases.abox]
  rw [huniv, MeasureTheory.setIntegral_univ]
  have hG : G = fun _ : Submission.BoseGases.X 0 => G 0 :=
    funext fun r => by rw [Subsingleton.elim r 0]
  rw [hG, MeasureTheory.integral_const]
  have hv : (volume : Measure (Submission.BoseGases.X 0)) Set.univ = 1 := by
    rw [← huniv, Submission.BoseGases.abox_volume 0 ℓ hℓ.le]
    norm_num
  simp only [MeasureTheory.Measure.real, hv, ENNReal.toReal_one, one_smul]

/-- **At one particle the excited count is the box mean-free mass of the state.**  This is the
`n = 0` case of `Work.BSKinetic.cnPlus_eq_slotSum`: the empty configuration space contributes no
integral, and `kcInsN 0 0 (z, ·)` is the one-particle configuration `fun _ => z`. -/
lemma cnPlus_one_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (φ : Submission.BoseGases.X 1 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    Submission.BoseGases.cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BSKinetic.slotFun1 φ z
            - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ,
                Work.BSKinetic.slotFun1 φ z') ^ 2 := by
  rw [Work.BSKinetic.cnPlus_eq_slotSum (ℓ := ℓ) hℓ 0 φ hφ, Fin.sum_univ_one]
  rw [integral_X0 (ℓ := ℓ) hℓ (G := fun r => ∫ z in Submission.BoseGases.acube ℓ,
      (φ (Submission.BoseGases.kcInsN 0 0 (z, r))
        - (ℓ ^ 3)⁻¹ * ∫ w in Submission.BoseGases.acube ℓ,
            φ (Submission.BoseGases.kcInsN 0 0 (w, r))) ^ 2)]
  have hkc : ∀ z : E3,
      Submission.BoseGases.kcInsN 0 0 (z, (0 : Submission.BoseGases.X 0))
        = fun _ : Fin 1 => z := by
    intro z
    ext j
    fin_cases j
    simp [Submission.BoseGases.kcInsN]
  simp only [hkc, Work.BSKinetic.slotFun1]

/-- The anchored gap word is `bℓ⁻²` times the box mean-free mass. -/
lemma gapWord_zero {ℓ b : ℝ} (ψ : E3 → ℝ) :
    Work.BoseKinLoc.gapWord ℓ b 0 ψ
      = b * ℓ ^ (-2 : ℤ) *
          ∫ z in Submission.BoseGases.acube ℓ,
            (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 := by
  simp only [Work.BoseKinLoc.gapWord, Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree,
    lamBox_zero]
  have hpt : ∀ z : E3, Work.BSKinetic.bsQ ℓ 0 ψ z ^ 2
      = (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 :=
    fun z => by rw [bsQ_zero_apply]
  rw [MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) (fun z _ => hpt z)]

/-- The anchored Neumann word is `½ε_T(dℓ)⁻²` times the box Neumann fraction of `Q_0ψ`. -/
lemma neuWord_zero {ℓ d εT : ℝ} (ψ : E3 → ℝ) :
    Work.BoseKinLoc.neuWord ℓ d εT 0 ψ
      = (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) *
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
            (Work.BSKinetic.bsQ ℓ 0 ψ) := by
  simp only [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.Qfree]

/-- The anchored main word is the two-cut mixture applied to the Fourier weight of `χ_ℓ(ψ−M)`. -/
lemma mainWord_zero_eq {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖) *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
            Submission.BoseGases.chiScale ℓ z *
              (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z')) p‖ ^ 2 := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  set hst : E3 → ℝ := fun z =>
    Submission.BoseGases.chiScale ℓ z *
      (ψ z - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') with hstdef
  have hstate : ContDiff ℝ (⊤ : ENat) hst :=
    (Submission.BoseGases.chiScale_contDiff hℓne).mul (hψ.sub contDiff_const)
  have hsupp : HasCompactSupport hst :=
    (Submission.BoseGases.chiScale_hasCompactSupport hℓne).mul_right
  have hint1 := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
    (c := (2 * (s * ℓ))⁻¹) hstate hsupp
  have hint2 := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
    (c := (2 * (d * s * ℓ))⁻¹) hstate hsupp
  have hfun : (fun z : E3 => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ))
      = fun z : E3 => (hst z : ℂ) := by
    funext z
    rw [Work.BSKinetic.bsWin, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, hstdef]
    simp only [smul_zero, sub_zero, zero_add, Complex.ofReal_mul]
  have hbase : ∀ F : ℝ → ℝ,
      Work.BSKinetic.bsOneBody ℓ F 0 ψ
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
            F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi hst p‖ ^ 2 := by
    intro F
    simp only [Work.BSKinetic.bsOneBody, Work.BSKinetic.Decomp.bsPsi, hfun]
  set G1 : E3 → ℝ := fun p =>
    Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi hst p‖ ^ 2 with hG1def
  set G2 : E3 → ℝ := fun p =>
    Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi hst p‖ ^ 2 with hG2def
  have hint1' : Integrable G1 := hint1
  have hint2' : Integrable G2 := hint2
  have hlin : (∫ p : E3, ((1 - εT) * G1 p + εT * G2 p))
      = (1 - εT) * (∫ p : E3, G1 p) + εT * (∫ p : E3, G2 p) := by
    rw [integral_add (hint1'.const_mul _) (hint2'.const_mul _), integral_const_mul,
      integral_const_mul]
  have hkey : (∫ p : E3,
        ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
          + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖) *
        ‖Work.BSKinetic.Decomp.bsPsi hst p‖ ^ 2)
      = ∫ p : E3, ((1 - εT) * G1 p + εT * G2 p) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hG1def, hG2def]
    ring
  simp only [Work.BoseKinLoc.mainWord, hbase]
  rw [hkey, hlin]
  ring

/-! ## 2. The small-box word `sbKin` and its integral split

`sbKin v μ M u φ` is `Work.UBBInputs8.tBwordBInd 1 ℓ d ε_T c_sb u φ`, i.e. FS `eq:appTB`'s word
`tbGapCoeff (ℓd) ε_T·cnPlusBoxInd + tBwordKinInd` at the sliding box `B(u)`.  Splitting
`∫_u sbKin` into the two halves is the point where the **marginal** `u`-integrability of each
half is used (Mathlib's Bochner integral is `0` on non-integrable functions, so the split needs
`Integrable` of *both* summands — see `FINDING_sbWord_marginal_integrable_missing_hv1.md` and
`Work.BoseFixB1.integrable_sbKin`). -/

/-- **The integral of `sbKin` splits** into its gap and spectral halves, given the *marginal*
integrability of each (Mathlib's Bochner integral is `0` on non-integrable functions, so the split
needs `Integrable` of *both* summands — `FINDING_sbWord_marginal_integrable_missing_hv1.md`,
`Work.BoseFixB1.integrable_sbKin`). -/
lemma integral_sbKin_split {v : E3 → ℝ} (μ : ℝ) (M : ℕ)
    (φ : Submission.BoseGases.X 1 → ℝ)
    (hint₁ : Integrable (fun u : E3 => Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) φ))
    (hint₂ : Integrable (fun u : E3 => Work.UBBInputs8.tBwordKinInd
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) φ)) :
    (∫ u : E3, sbKin (v := v) μ M u φ)
      = Work.SmallBoxTBWord.tbGapCoeff
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
          (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) φ)
        + ∫ u : E3, Work.UBBInputs8.tBwordKinInd
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) φ := by
  have hfun : (fun u : E3 => sbKin (v := v) μ M u φ)
      = fun u : E3 => Work.SmallBoxTBWord.tbGapCoeff
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
            Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) φ
          + Work.UBBInputs8.tBwordKinInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) φ := by
    funext u
    rw [Work.BoseFixB1.sbKin, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd]
  rw [hfun, MeasureTheory.integral_add hint₁ hint₂, MeasureTheory.integral_const_mul]

end Work.BoseFixB1
