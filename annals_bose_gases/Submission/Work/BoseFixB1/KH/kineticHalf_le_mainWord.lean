import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Core.symA_fsKinCoeff_mix_scaled
import Submission.Work.BoseFixB1.KH.SymAMoments
import Submission.Work.BoseFixB1.KH.corr.corrInputB1KH
import Submission.Work.BoseFixB1.oneBodyKineticHalfArith
import Submission.Work.BoseFixB1S.cruxUnprojB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.KH.kineticHalf_le_mainWord` — the `φ`-form of the sliding spectral half

Everything in this file is proved.  The final theorem `kineticHalf_le_mainWord` is the transport
`kineticHalf_le_mainWord_of_inputs` applied to its three inputs; of these, the mean-mismatch
residual `Work.BoseFixB1S.CorrInput v` is delegated to
`Submission/Work/BoseFixB1/KH/corr/corrInputB1KH.lean` (`Work.BoseFixB1.KH.corr.corrInputB1KH`),
while the other two are supplied here.  The proved pieces:

* the bridge `tBwordKinInd_eq_bsW'` (a local copy of `Work.OneBodyTwoCut.tBwordKinInd_eq_bsW`,
  reproduced because `Submission.Work.OneBodyTwoCut.Bridge` is currently blocked by an unrelated
  parse failure in `Submission.Work.UBB.PaperTheorem`),
* `cnPlus_one_eq'`, `mainWord_zero_eq'` (local copies of the `N = 1` bookkeeping of
  `Work.BoseFixB1.oneBodyKineticHalfAux`, same reason),
* `fsParams_criteriaB` (the FS-parameter criteria: `d ≤ 1/2`, `eT ≤ 1/2`, `M₁ ≤ 1/s`,
  `8M₂ ≤ (1−d)²/s²`),
* `unprojInputB1` (the `fsKinCoeff` instance of the *proved* `Work.BoseFixB1S.cruxUnprojB1`),
* `mixInputB1` (the two-cut symbol comparison at FS's parameters, from the *proved*
  `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` + `fsParams_criteriaB`),
* `kineticHalf_le_mainWord_of_inputs` (the transport: the crux of
  `Work.BoseFixB1S.kineticCruxParsed_of_inputs` in the `φ`-form of the target).

See `FINDING_kineticHalf_le_mainWord.md` (same directory) for the reduction and for the shape of
the one remaining estimate. -/

noncomputable section

namespace Work.BoseFixB1.KH

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The bridge `tBwordKinInd = (2π)⁻³·bsW` -/

/-- **The sliding spectral half is an explicit Fourier integral** (local copy of
`Work.OneBodyTwoCut.tBwordKinInd_eq_bsW`). -/
theorem tBwordKinInd_eq_bsW' {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (φ : X1 → ℝ) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u) c φ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
            (φ (fun _ : Fin 1 => z)
              - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                * ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z'))) := by
  have hχ : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiB ℓ d u z = 0 := fun z hz => by
    by_contra h
    exact hz (Submission.BoseGases.chiB_support_mem hℓ hd u z h)
  rw [Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (Submission.BoseGases.fsKinCoeff c) φ hχ,
    Work.BSKinetic.tBdiagForm_one_eq_bsW (a := ℓ) hℓ]

/-! ## 1. The `N = 1` bookkeeping of `cnPlus` and `mainWord` -/

/-- The integral over the empty configuration space `X 0` is evaluation at the unique point. -/
lemma integral_X0' {ℓ : ℝ} (hℓ : 0 < ℓ) (G : Submission.BoseGases.X 0 → ℝ) :
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

/-- **At one particle the excited count is the box mean-free mass of the state.** -/
lemma cnPlus_one_eq' {ℓ : ℝ} (hℓ : 0 < ℓ) (φ : X1 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    Submission.BoseGases.cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BSKinetic.slotFun1 φ z
            - (ℓ ^ 3)⁻¹ * ∫ z' in Submission.BoseGases.acube ℓ,
                Work.BSKinetic.slotFun1 φ z') ^ 2 := by
  rw [Work.BSKinetic.cnPlus_eq_slotSum (ℓ := ℓ) hℓ 0 φ hφ, Fin.sum_univ_one]
  rw [integral_X0' (ℓ := ℓ) hℓ (G := fun r => ∫ z in Submission.BoseGases.acube ℓ,
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

/-- **The anchored main word is the two-cut mixture applied to the Fourier weight of
`χ_ℓ(ψ − M)`** (local copy of `Work.BoseFixB1.mainWord_zero_eq`). -/
lemma mainWord_zero_eq' {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ}
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

/-! ## 2. The FS-parameter criteria -/

/-- **The FS-parameter criteria** feeding `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` at
`a = ℓ·d`, `C = s⁻¹`.  At diluteness `t = μ(a v)³ ≤ symAEps0` one has `s = t^{1/323} ≤ δ`
with `δ = min 2⁻¹ (min (M₁+1)⁻¹ (32M₂+1)⁻¹)`, and then all four criteria follow by monotonicity
of `x ↦ x ^ r` and elementary arithmetic. -/
theorem fsParams_criteriaB {v : E3 → ℝ} :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 / 2
      ∧ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2
      ∧ Work.BoseFixB1.KH.symAMom1 ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
      ∧ 8 * Work.BoseFixB1.KH.symAMom2
          ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ^ 2 := by
  have hδ0 : 0 < Work.BoseFixB1.KH.symASmallScale := Work.BoseFixB1.KH.symASmallScale_pos
  have hδhalf : Work.BoseFixB1.KH.symASmallScale ≤ 1 / 2 :=
    Work.BoseFixB1.KH.symASmallScale_le_half
  have hδM1 : Work.BoseFixB1.KH.symASmallScale ≤ (Work.BoseFixB1.KH.symAMom1 + 1)⁻¹ :=
    Work.BoseFixB1.KH.symASmallScale_le_mom1
  have hδM2 : Work.BoseFixB1.KH.symASmallScale ≤ (32 * Work.BoseFixB1.KH.symAMom2 + 1)⁻¹ :=
    Work.BoseFixB1.KH.symASmallScale_le_mom2
  refine ⟨Work.BoseFixB1.KH.symAEps0, Work.BoseFixB1.KH.symAEps0_pos, fun μ hAdm => ?_⟩
  have hμ : 0 < μ := hAdm.1
  have hav : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have htle : μ * (_root_.BoseGases.a v) ^ 3 ≤ Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ) :=
    hAdm.2.1
  have hs0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  -- `s = t^{1/323} ≤ δ`
  have hsle : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤
      Work.BoseFixB1.KH.symASmallScale := by
    have h1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) := by
      simp only [Work.BoseFixB1.paramsAt_eq_fsParams, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    rw [h1]
    have h2 : (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)
        ≤ (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) :=
      Real.rpow_le_rpow ht0.le htle (by norm_num)
    have h3 : (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ ((1 : ℝ) / 323)
        = Work.BoseFixB1.KH.symASmallScale := by
      rw [← Real.rpow_mul hδ0.le,
        show (323 : ℝ) * ((1 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
    rwa [h3] at h2
  -- `d = t^{6/323} ≤ 1/2`
  have hdle : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 / 2 := by
    have h1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323) := by
      simp only [Work.BoseFixB1.paramsAt_eq_fsParams, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    rw [h1]
    have h2 : (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323)
        ≤ (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ ((6 : ℝ) / 323) :=
      Real.rpow_le_rpow ht0.le htle (by norm_num)
    have h3 : (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ ((6 : ℝ) / 323)
        = Work.BoseFixB1.KH.symASmallScale ^ (6 : ℝ) := by
      rw [← Real.rpow_mul hδ0.le, show (323 : ℝ) * ((6 : ℝ) / 323) = 6 by norm_num]
    have h4 : Work.BoseFixB1.KH.symASmallScale ^ (6 : ℝ) ≤ ((1 : ℝ) / 2) ^ (6 : ℝ) :=
      Real.rpow_le_rpow hδ0.le hδhalf (by norm_num)
    have h5 : ((1 : ℝ) / 2) ^ (6 : ℝ) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_ge (show (0 : ℝ) < 1 / 2 by norm_num)
        (by norm_num) (show (1 : ℝ) ≤ 6 by norm_num)
      simpa [Real.rpow_one] using h
    rw [h3] at h2
    linarith [h2, h4, h5]
  -- `eT = t^{(23/4)/323} ≤ 1/2`
  have hTle : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 := by
    have h1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323) := by
      simp only [Work.BoseFixB1.paramsAt_eq_fsParams, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    rw [h1]
    have h2 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (((23 : ℝ) / 4) / 323)
        ≤ (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ (((23 : ℝ) / 4) / 323) :=
      Real.rpow_le_rpow ht0.le htle (by norm_num)
    have h3 : (Work.BoseFixB1.KH.symASmallScale ^ (323 : ℝ)) ^ (((23 : ℝ) / 4) / 323)
        = Work.BoseFixB1.KH.symASmallScale ^ ((23 : ℝ) / 4) := by
      rw [← Real.rpow_mul hδ0.le,
        show (323 : ℝ) * (((23 : ℝ) / 4) / 323) = (23 : ℝ) / 4 by norm_num]
    have h4 : Work.BoseFixB1.KH.symASmallScale ^ ((23 : ℝ) / 4)
        ≤ ((1 : ℝ) / 2) ^ ((23 : ℝ) / 4) :=
      Real.rpow_le_rpow hδ0.le hδhalf (by norm_num)
    have h5 : ((1 : ℝ) / 2) ^ ((23 : ℝ) / 4) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_ge (show (0 : ℝ) < 1 / 2 by norm_num)
        (by norm_num) (show (1 : ℝ) ≤ (23 : ℝ) / 4 by norm_num)
      simpa [Real.rpow_one] using h
    rw [h3] at h2
    linarith [h2, h4, h5]
  -- the moment criteria from `s ≤ δ ≤ (M₁+1)⁻¹` and `s ≤ δ ≤ (32M₂+1)⁻¹`
  have hsM1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      * (Work.BoseFixB1.KH.symAMom1 + 1) ≤ 1 := by
    have h1 : 0 < Work.BoseFixB1.KH.symAMom1 + 1 := by
      linarith [Work.BoseFixB1.KH.symAMom1_nonneg]
    calc (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * (Work.BoseFixB1.KH.symAMom1 + 1)
        ≤ Work.BoseFixB1.KH.symASmallScale * (Work.BoseFixB1.KH.symAMom1 + 1) :=
          mul_le_mul_of_nonneg_right hsle (le_of_lt h1)
      _ ≤ (Work.BoseFixB1.KH.symAMom1 + 1)⁻¹ * (Work.BoseFixB1.KH.symAMom1 + 1) :=
          mul_le_mul_of_nonneg_right hδM1 (le_of_lt h1)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  have hsM2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      * (32 * Work.BoseFixB1.KH.symAMom2 + 1) ≤ 1 := by
    have h1 : 0 < 32 * Work.BoseFixB1.KH.symAMom2 + 1 := by
      linarith [Work.BoseFixB1.KH.symAMom2_nonneg]
    calc (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (32 * Work.BoseFixB1.KH.symAMom2 + 1)
        ≤ Work.BoseFixB1.KH.symASmallScale * (32 * Work.BoseFixB1.KH.symAMom2 + 1) :=
          mul_le_mul_of_nonneg_right hsle (le_of_lt h1)
      _ ≤ (32 * Work.BoseFixB1.KH.symAMom2 + 1)⁻¹ * (32 * Work.BoseFixB1.KH.symAMom2 + 1) :=
          mul_le_mul_of_nonneg_right hδM2 (le_of_lt h1)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  refine ⟨hdle, hTle, ?_, ?_⟩
  · -- `M₁ ≤ 1/s`
    have hsne : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 := ne_of_gt hs0
    have h2 : Work.BoseFixB1.KH.symAMom1 + 1
        ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := by
      have h3 := mul_le_mul_of_nonneg_right hsM1 (inv_nonneg.mpr hs0.le)
      have h4 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (Work.BoseFixB1.KH.symAMom1 + 1)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
          = Work.BoseFixB1.KH.symAMom1 + 1 := by
        field_simp
      rw [h4, one_mul] at h3
      exact h3
    have h4 : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := inv_pos.mpr hs0
    linarith
  · -- `8M₂ ≤ (1−d)²/s²`
    have hs_half : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ 1 / 2 :=
      le_trans hsle hδhalf
    have hd_half : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 / 2 := hdle
    have hsne : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 := ne_of_gt hs0
    -- `8 M₂ ≤ (1−s)/(4s)`
    have h32 : 32 * Work.BoseFixB1.KH.symAMom2
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by
      have h3 := mul_le_mul_of_nonneg_right hsM2 (inv_nonneg.mpr hs0.le)
      have h4 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (32 * Work.BoseFixB1.KH.symAMom2 + 1)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
          = 32 * Work.BoseFixB1.KH.symAMom2 + 1 := by
        field_simp
      rw [h4, one_mul] at h3
      have h5 : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
          = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ - 1 := by
        field_simp
      rw [div_eq_mul_inv, h5]
      linarith
    have h8 : 8 * Work.BoseFixB1.KH.symAMom2
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          / (4 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) := by
      have h4 : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          / (4 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          = ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
              / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) / 4 := by
        field_simp
      rw [h4]
      linarith [h32]
    refine le_trans h8 ?_
    -- `(1−s)/(4s) ≤ s(1−s)/4 · (1/s²)`
    rw [show (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          / (4 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
        = (1 / ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 2))
          * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              * (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)) / 4) by
      field_simp]
    -- and `s(1−s)/4 · (1/s²) ≤ (1−d)²/s²`
    rw [show (1 / ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 2))
          * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              * (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)) / 4)
        = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            * (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)) / 4
          / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 2 by
      field_simp]
    rw [show (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ^ 2
        = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 2 by
      field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)) / 4
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by
      nlinarith [hs_half, hd_half, hs0,
        sq_nonneg ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s - 1 / 2)]
    exact mul_le_mul_of_nonneg_right hprod (by positivity)

/-! ## 3. The two inputs of `kineticCruxParsed_of_inputs` that are available -/

/-- **The unprojected family-form input** (the `fsKinCoeff` instance of the proved
`Work.BoseFixB1S.cruxUnprojB1`). -/
theorem unprojInputB1 : Work.BoseFixB1S.UnprojInput :=
  fun a c ha hc ψ hψ hcs => Work.BoseFixB1S.cruxUnprojB1 ha hc hψ hcs

/-- **The two-cut symbol comparison at FS's parameters** (`Work.BoseFixB1S.MixInput`) from the
proved `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` and `fsParams_criteriaB`. -/
theorem mixInputB1 {v : E3 → ℝ} : Work.BoseFixB1S.MixInput v := by
  obtain ⟨ε₀, hε₀, hcrit⟩ := fsParams_criteriaB (v := v)
  refine ⟨ε₀, hε₀, fun μ hAdm q => ?_⟩
  obtain ⟨hdle, hTle, hM1, hM2⟩ := hcrit μ hAdm
  have hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hs0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hM1' : ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3,
      (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖
      ≤ (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) := by
    rw [one_div, ← Work.BoseFixB1.KH.symAMom1]
    exact hM1
  have hM2' : 8 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3,
      (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2)
      ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
        * (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 2 := by
    rw [one_div, ← Work.BoseFixB1.KH.symAMom2]
    exact hM2
  have h := Work.BoseFixB1.symA_fsKinCoeff_mix_scaled
    (a := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (C := 1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (β := Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
      ((1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) / 2)) 0)
    (mul_pos hℓ0 hd0) (by positivity) (le_of_lt hd0) hdle heT0 hTle hM1' hM2' le_rfl q
  -- rewrite the transport's shapes into the goal's shapes
  have e1 : (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      = Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) := by
    rw [Work.BoseFixB1.sbCut]
    field_simp
  have e2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))
      = (2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹ := by
    field_simp
  have e3 : (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))
      = (2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹ := by
    field_simp
  have e4 : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
        ((1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) / 2)) 0
      / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
      = ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
        * Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
            ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0 := by
    rw [show (1 / (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) / 2
        = (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ by field_simp]
    ring
  rw [e1, e2, e3, e4] at h
  exact h

/-! ## 4. The transport of the crux to the `φ`-form -/

/-- **The target from the three inputs of `Work.BoseFixB1S.kineticCruxParsed_of_inputs`.** -/
theorem kineticHalf_le_mainWord_of_inputs {v : E3 → ℝ}
    (hcorr : Work.BoseFixB1S.CorrInput v) (hunproj : Work.BoseFixB1S.UnprojInput)
    (hmix : Work.BoseFixB1S.MixInput v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (∫ u : E3,
            Work.UBBInputs8.tBwordKinInd
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) φ)
          ≤ Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0
                (Work.BSKinetic.slotFun1 φ)
            + (Work.BoseBox.bValue / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
                * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ := by
  obtain ⟨ε₀, hε₀, hcrux⟩ :=
    Work.BoseFixB1S.kineticCruxParsed_of_inputs hcorr hunproj hmix
  refine ⟨ε₀, hε₀, fun μ hAdm φ hφ => ?_⟩
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓe
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hde
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hse
  set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTe
  set cc : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hcce
  set ψ : E3 → ℝ := Work.BSKinetic.slotFun1 φ with hψe
  have hℓ0 : 0 < ℓ := by rw [hℓe]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < d := by rw [hde]; exact Work.BoseFixB1.adm_d_pos hAdm
  have hψc : ContDiff ℝ (⊤ : ENat) ψ := by
    rw [hψe]; exact hφ.comp (by fun_prop)
  have hφψ : (fun x : X1 => ψ (x 0)) = φ := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext j; fin_cases j; rfl
    rw [hψe, Work.BSKinetic.slotFun1, hx]
  -- (1) the left side, pointwise
  have hL : (∫ u : E3,
        Work.UBBInputs8.tBwordKinInd ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.chiB ℓ d u) cc φ)
      = ∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ *
          Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
            (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
              (ψ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                * ∫ z' in Submission.BoseGases.dlBox ℓ d u, ψ z')) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simpa only [← hφψ] using tBwordKinInd_eq_bsW' hℓ0 hd0 u φ
  -- (2) the crux
  have hcr := hcrux μ hAdm ψ hψc
  -- (3) the right side: `mainWord`
  have hmain := mainWord_zero_eq' (ℓ := ℓ) (d := d) (s := s) (εT := eT) hℓ0 (ψ := ψ) hψc
  have hmain' : Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          ((1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖
            + eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖) *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) *
              ((ψ z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, ψ z' : ℝ) : ℂ)) q‖ ^ 2 := by
    rw [hmain]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Work.BSKinetic.Decomp.bsPsi, Complex.ofReal_mul, one_div]
  -- (4) the right side: `cnPlus`
  have hcn : Submission.BoseGases.cnPlus ℓ φ
      = ∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2 := by
    rw [cnPlus_one_eq' hℓ0 φ hφ]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      fun z _ => ?_
    rw [← hψe, ← one_div]
  -- (5) assemble
  simp only [← hℓe, ← hde, ← hse, ← heTe, ← hcce] at hcr
  rw [hL, hmain', hcn]
  exact hcr

/-! ## 5. The target -/

/-- The **assembly-ready form** of the sliding spectral half: the `u`-integral of the sliding
kinetic word `tBwordKinInd` at `N = 1` is dominated by the *anchored* two-cut word
`Work.BoseKinLoc.mainWord` plus the box-restricted flat payment `(bValue/2ℓ²)·cnPlus ℓ φ`.
This is the `φ`-form of `Work.BoseFixB1.KH.kineticHalfCrux` (which is phrased for the mean-free
state `η = ψ − M`, `ψ = slotFun1 φ`, `M = ⍍_{acube ℓ}ψ`) and the two are equivalent modulo
proved lemmas, so the cleanest route is:

* `Work.OneBodyTwoCut.tBwordKinInd_eq_bsW hℓ hd u φ` rewrites the left integrand as
  `(2π)⁻³ bsW (fsKinCoeff c) (χ_{B(u)}(ψ − m_u))`, `m_u = ⍍_{B(u)}ψ`;
* `χ_{B(u)}(ψ − m_u) = χ_{B(u)}(η − n_u)`, `n_u = ⍍_{B(u)}η` — the two box means differ by the
  constant `M`, so this is an identity wherever `boxMass ℓ d u ≠ 0`; where `boxMass = 0` the box
  `dlBox ℓ d u` has empty interior, so `χ_{B(u)} ≡ 0`;
* then apply `Work.BoseFixB1.KH.kineticHalfCrux h` at `η := ψ − M`, whose right side is
  `mainWord ℓ P.d P.s P.eT 0 ψ + (bValue/(2ℓ²))·∫_{acube ℓ}η²` by
  `Work.BoseFixB1.mainWord_zero_eq` and `Work.BoseFixB1.cnPlus_one_eq`;
* the `ε₀` is the crux's.

The transport is `kineticHalf_le_mainWord_of_inputs`: its three inputs are the mean-mismatch
residual `Work.BoseFixB1S.CorrInput` (the remaining gap), the unprojected family form
`unprojInputB1` and the two-cut symbol comparison `mixInputB1`. -/
theorem kineticHalf_le_mainWord {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.UBBInputs8.tBwordKinInd
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) φ)
          ≤ Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0
                (Work.BSKinetic.slotFun1 φ)
            + (Work.BoseBox.bValue / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
                * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ :=
  kineticHalf_le_mainWord_of_inputs (Work.BoseFixB1.KH.corr.corrInputB1KH h) unprojInputB1
    (mixInputB1 (v := v))

end Work.BoseFixB1.KH
