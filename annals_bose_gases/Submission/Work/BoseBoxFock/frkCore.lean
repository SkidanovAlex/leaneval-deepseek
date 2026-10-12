import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PotCubicResiduals
import Submission.Work.BoseBoxFock.kinRow_lattice
import Submission.Work.BoseBoxFock.potTruncRepair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK` — the shared vocabulary and the PROVED glue of the repaired
# `FormRowKin` route (design v2)

This module is the *vocabulary* half of `LEAD_DESIGN_formrowkin_v2.md`: the definitions
(`symOp`, `OBineq`, `OBineq4`, `kappaHon`, `FormRowKin4`, `FormW2BpotG`, `PotCubicG`,
`PotCubicLowBandG`, `LowBandNPlusLinear`, `LowBandArith`) and the **proved** glue of the
reserve-transfer route (`oneBody_kinGroup_le`, `oneBody_kinGroup_le4`, `PotCubicG_of_free_lowG`,
`FormW2BpotG_of_potGroups`, `PotCubicG_mono`, `FormW2BpotG_exists`, `RowB_of_kin4_potG`,
`cnPlus_nonneg'`, `cred_nonneg`, `FormRowKin_of_FormRowKin4`, `PotCubicLowBandG_of_nplus`,
`gapBare_nonneg`, `momForm_nonneg`).

The **leaves** (the analytic statements W0–W4, S1, R-τ, R-η, the regime gate `G`, the dictionary
`D4` and `neuWord_nonneg_general`) are declared in their own modules of this namespace, which
import this one; the **assembly** theorems (`FormRowKin4_holds_assembled`, `FormRowKin_holds_v2`,
`PotCubicG_exists`, `RowB_existsG`, `box_to_model_assembledG`) live in
`Submission/Work/BoseBoxFock/frkAssemble.lean`, which imports the leaves.

⚠ The `(T)`-route family (`tauPhi_row_closedBall`, `tauPhi_row_direct`, `sharpShiftRow`,
`tauPhi_row_lowMomentum`) is CANCELLED: (T) is FALSE for large `cℓ`.  Do not extend it.
-/

noncomputable section
open MeasureTheory
namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)


/-- (W1) lattice/periodisation identity for a symbol `σ` (polarised Fourier-series Parseval on the
cell; template `latHeat_periodisation_aux`).  `symOp σ g x = (2π)⁻³∫σ(p)ĝ(p)e^{ipx}dp`. -/
def symOp (σ : E3 → ℝ) (g : E3 → ℂ) (x : E3) : ℂ :=
  ((2 * Real.pi) ^ 3 : ℝ)⁻¹ • ∫ p : E3,
    Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * ((σ p : ℝ) : ℂ) *
      Submission.BoseGases.kinFT g p


/-- (OB) the one-body kinetic-group inequality (all three rows + reserve), per fibre. -/
theorem oneBody_kinGroup_le {Kτ Kη : ℝ} (hKτ : 0 ≤ Kτ) (hKη : 0 ≤ Kη)
    (hτ : ∀ {ℓ s d eT : ℝ}, 0 < ℓ → 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 →
      ∀ (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
          + Kτ * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hη : ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ + Kη * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    {ℓ s d eT b κ : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d) (hd1 : d ≤ 1) (heT : 0 ≤ eT)
    (heT1 : eT ≤ 1) (hb : 0 < b) (hκ : (d ^ 2 * ℓ)⁻¹ ≤ κ)
    (hsb : Kτ * s ≤ b / 5) (hdb : eT * Kη * d ^ 4 ≤ 12)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hgap0 : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ) (hmom0 : 0 ≤ Work.BoseKinLoc.momForm ℓ d 0 ψ)
    (hneu0 : 0 ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ) :
    (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
      + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
        - b / 100 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ
            + eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ) := by
  have h1 := hτ hℓ hs hd hd1 heT heT1 N ψ hψ
  have h2 := hη hℓ hd hd1 hκ fu N ψ hψ
  set G := Work.BoseKinLoc.gapBare ℓ 0 ψ
  set Mo := Work.BoseKinLoc.momForm ℓ d 0 ψ
  set Sτ := (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
  set Sη := (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
  have hfsT : Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
      = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + b * ℓ ^ (-2 : ℤ) * G
        + b * eT * (d * ℓ) ^ (-2 : ℤ) * Mo + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := rfl
  rw [hfsT]
  have hl2 : ℓ ^ (-2 : ℤ) = (ℓ ^ 2)⁻¹ := by simp [zpow_neg]
  have hdl2 : (d * ℓ) ^ (-2 : ℤ) = (d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ := by
    rw [zpow_neg, ← mul_inv, ← mul_pow]; norm_cast
  rw [hl2, hdl2]
  have hℓ2 : 0 < (ℓ ^ 2)⁻¹ := by positivity
  have hd2 : 0 < (d ^ 2)⁻¹ := by positivity
  -- η_H row: (eT b /(2 d² ℓ²))(1/32) Sη ≤ (eT b /(d²ℓ²))·(24/64) Mo + b ℓ⁻² (eT Kη d⁴/64) G
  have hηrow : eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * Sη)
      ≤ (3 / 8) * (b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo)
        + b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G := by
    have hc : 0 ≤ eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h2 hc
    have e1 : eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * Sη)
        = eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) * Sη := by ring
    have e2 : eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) * (24 * Mo + Kη * d ^ 6 * G)
        = (3 / 8) * (b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo)
          + b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G := by
      field_simp
      ring
    rw [e1]; linarith [this, e2.le, e2.ge]
  have hgapτ : Kτ * s * (ℓ ^ 2)⁻¹ * G ≤ (b / 5) * (ℓ ^ 2)⁻¹ * G := by
    have := mul_le_mul_of_nonneg_right hsb (mul_nonneg hℓ2.le hgap0)
    nlinarith [this]
  have hgapη : b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G ≤ (3 / 16 * b) * (ℓ ^ 2)⁻¹ * G := by
    have h16 : eT * Kη * d ^ 4 / 64 ≤ 3 / 16 := by linarith
    have hbg : 0 ≤ b * (ℓ ^ 2)⁻¹ * G := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h16 hbg]
  have hmo : 0 ≤ b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo := by positivity
  have hb2 : b / (2 * ℓ ^ 2) * G = (b / 2) * (ℓ ^ 2)⁻¹ * G := by
    field_simp
  rw [hb2]
  nlinarith [h1, hηrow, hgapτ, hgapη, hmo, hneu0, mul_nonneg hb.le (mul_nonneg hℓ2.le hgap0)]


/-- The one-body kinetic-group inequality as a `Prop` (the conclusion of `oneBody_kinGroup_le`). -/
def OBineq (ℓ s d eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ) : Prop :=
    (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
      + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
        - b / 100 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ
            + eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ)


/-- The honest `η_H` onset parameter, verbatim from `HonestBoxFam`. -/
def kappaHon (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2)
    ^ (-(1 : ℝ)) * Real.sqrt (μ * BoseGases.a v)


theorem gapBare_nonneg (ℓ : ℝ) (ψ : E3 → ℝ) : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  unfold Work.BoseKinLoc.gapBare
  exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _


theorem momForm_nonneg (ℓ d : ℝ) (ψ : E3 → ℝ) : 0 ≤ Work.BoseKinLoc.momForm ℓ d 0 ψ := by
  unfold Work.BoseKinLoc.momForm
  refine mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun p => ?_)
  unfold Work.BoseKinLoc.momProj
  split_ifs <;> positivity


/-! # v2 PART B — the reserve transfer, additively (no edit of frozen defs) -/

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
open Work.BoseB4 Work.BoseDict
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false


/-- `FormRowKin` with the `cnPlus` reserve raised from `b/100` to `b/4` (the extra `γ = b/4 − b/100`). -/
noncomputable def FormRowKin4 (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      (∅ : Finset (Lab (HM μ).N))
                      (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      0
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
                    (Φ : Submission.BoseGases.X n → ℝ)
                  - ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
                  - ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) *
                      (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
                          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                              (Φ : Submission.BoseGases.X n → ℝ)
                        + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT *
                            ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                              * Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-2 : ℤ)
                          * Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                              (Φ : Submission.BoseGases.X n → ℝ))
                  + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ



/-- `FormW2Bpot` credited with `γ·ℓ⁻²cnPlus`. -/
noncomputable def FormW2BpotG (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
                  + ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
                  + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ



/-- `PotCubic` credited with `γ·ℓ⁻²cnPlus` (FS pay the cubic low band from this gap). -/
noncomputable def PotCubicG (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFix.q3lowWord fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ



/-- The low band re-filed against `PotCubicG` (UNPROVED; route: `LowBandNPlusLinear` + `LowBandArith`). -/
noncomputable def PotCubicLowBandG (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              - (∫ x : Submission.BoseGases.X n,
                  star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                    * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                        (Work.BoseB7.excited (Lab (HM μ).N))
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ


/-- (LB1) the `n₊`-LINEAR operator bound of the low band (UNPROVED leaf; FINDING_PotCubic_exists §6.4). -/
noncomputable def LowBandNPlusLinear (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (J : ℝ) (Nmin : ℝ → ℕ) (ε₀ K : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              - (∫ x : Submission.BoseGases.X n,
                  star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                    * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                        (Work.BoseB7.excited (Lab (HM μ).N))
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ K * (((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)))
                  * (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s|)
                  * (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N) \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
                      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k|))
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)


/-- (LB2) the arithmetic of the low band against the transferred gap (UNPROVED leaf; margin ≈ 29·t^0.229). -/
noncomputable def LowBandArith (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (Nmin : ℝ → ℕ) (ε₀ K : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      K * (((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)))
        * (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s|)
        * (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N) \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
            |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k|))
        ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100)
          * Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)


variable {n : ℕ}


/-- The real part of the integral of a pointwise sum: two integrable terms, in the *distributed*
form used by the assembly. -/
private lemma integral_re_add2 {Ψ : Submission.BoseGases.X n → ℂ}
    {b₁ b₂ : Submission.BoseGases.X n → ℂ}
    (h1 : MeasureTheory.Integrable (fun x => star (Ψ x) * b₁ x))
    (h2 : MeasureTheory.Integrable (fun x => star (Ψ x) * b₂ x)) :
    (∫ x, star (Ψ x) * (b₁ x + b₂ x)).re
      = (∫ x, star (Ψ x) * b₁ x).re + (∫ x, star (Ψ x) * b₂ x).re := by
  have hp : (fun x : Submission.BoseGases.X n => star (Ψ x) * (b₁ x + b₂ x))
      = fun x => star (Ψ x) * b₁ x + star (Ψ x) * b₂ x := by
    funext x
    ring
  rw [hp, MeasureTheory.integral_add h1 h2, Complex.add_re]


/-- The real part of the integral of a pointwise sum of four integrable terms (in the grouping
`(a₀+a₁) + (a₂+a₃)` in which the split of `FormW2Bpot`'s left-hand side is stated). -/
private lemma integral_re_add4 {Ψ : Submission.BoseGases.X n → ℂ}
    {a₀ a₁ a₂ a₃ : Submission.BoseGases.X n → ℂ}
    (h0 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₀ x))
    (h1 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₁ x))
    (h2 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₂ x))
    (h3 : MeasureTheory.Integrable (fun x => star (Ψ x) * a₃ x)) :
    (∫ x, star (Ψ x) * ((a₀ x + a₁ x) + (a₂ x + a₃ x))).re
      = ((∫ x, star (Ψ x) * a₀ x).re + (∫ x, star (Ψ x) * a₁ x).re)
        + ((∫ x, star (Ψ x) * a₂ x).re + (∫ x, star (Ψ x) * a₃ x).re) := by
  have hA : MeasureTheory.Integrable (fun x => star (Ψ x) * (a₀ x + a₁ x)) :=
    (h0.add h1).congr (Filter.Eventually.of_forall (fun x => by
      rw [Pi.add_apply]; dsimp only; rw [mul_add]))
  have hB : MeasureTheory.Integrable (fun x => star (Ψ x) * (a₂ x + a₃ x)) :=
    (h2.add h3).congr (Filter.Eventually.of_forall (fun x => by
      rw [Pi.add_apply]; dsimp only; rw [mul_add]))
  rw [integral_re_add2 (b₁ := fun x => a₀ x + a₁ x) (b₂ := fun x => a₂ x + a₃ x) hA hB]
  rw [integral_re_add2 (b₁ := a₀) (b₂ := a₁) h0 h1,
    integral_re_add2 (b₁ := a₂) (b₂ := a₃) h2 h3]


/-- `errKafz v R μ` is additive in its constant, in the exact form used by the assembly. -/
private lemma errKafz_add (v : ℝ³ → ℝ) (R μ C₁ C₂ : ℝ) :
    Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
  simp only [Work.BoseFixR.errKafz]
  ring



theorem PotCubicG_of_free_lowG (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀₁ ε₀₂ C₁ C₂ : ℝ)
    (hfree : PotCubicFree v h fc fu R J Nmin ε₀₁ C₁)
    (hlow : PotCubicLowBandG v h fc fu R J Nmin ε₀₂ C₂) :
    PotCubicG v h fc fu R J Nmin (min ε₀₁ ε₀₂) (C₁ + C₂) := by
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin
    hKp hLp hθp T_NH hTNH
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₀₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₀₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have h1 := hfree HM hMono μ hAdm₁ hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth
    hint hemem hpin hKp hLp hθp T_NH hTNH
  have h2 := hlow HM hMono μ hAdm₂ hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth
    hint hemem hpin hKp hLp hθp T_NH hTNH
  have h3 : Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
    simp only [Work.BoseFixR.errKafz]; ring
  rw [h3]
  linarith



theorem FormW2BpotG_of_potGroups (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ)
    (h0 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotContactChem v h fc fu R J Nmin ε C)
    (h1 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotChiLin v h fc fu R J Nmin ε C)
    (h2 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotPairRows v h fc fu R J Nmin ε C)
    (h3 : ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ PotCubicG v h fc fu R J Nmin ε C)
    (hint : ∀ {ε₀ : ℝ}, PotGroupsIntegrable v h hav fc fu R J Nmin ε₀) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ FormW2BpotG v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hG0⟩ := h0
  obtain ⟨ε₁, C₁, hε₁, hC₁, hG1⟩ := h1
  obtain ⟨ε₂, C₂, hε₂, hC₂, hG2⟩ := h2
  obtain ⟨ε₃, C₃, hε₃, hC₃, hG3⟩ := h3
  refine ⟨min (min (min ε₀ ε₁) ε₂) ε₃, C₀ + C₁ + C₂ + C₃,
    lt_min (lt_min (lt_min hε₀ hε₁) hε₂) hε₃, by linarith, ?_⟩
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t h10θ
    T_NH hT
  -- ## the four threshold instances of `Adm` (`Adm` is monotone in its threshold)
  have hε' : μ * (BoseGases.a v) ^ 3 ≤ min (min (min ε₀ ε₁) ε₂) ε₃ := hAdm.2.1
  have hA0 : Work.BoseBoxFix.Adm v ε₀ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _))), hAdm.2.2⟩
  have hA1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _))), hAdm.2.2⟩
  have hA2 : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hε' (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hA3 : Work.BoseBoxFix.Adm v ε₃ μ :=
    ⟨hAdm.1, le_trans hε' (min_le_right _ _), hAdm.2.2⟩
  -- ## the four group inequalities, and the integrability of the four integrands
  have hg0 := hG0 HM hNmin μ hA0 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg1 := hG1 HM hNmin μ hA1 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg2 := hG2 HM hNmin μ hA2 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  have hg3 := hG3 HM hNmin μ hA3 hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t
    h10θ T_NH hT
  obtain ⟨hi0, hi1, hi2, hi3⟩ := hint (ε₀ := ε₀) HM hNmin μ hA0 hJ n Φ hn hnorm hlow hmom e h1m h2b
    h3s h4o h5i h6t h7θ h8q h9t h10θ T_NH hT
  -- ## the two rewritings of the right-hand side
  have hwords : Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
      = Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0)
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ)
          + Submission.BoseGases.q1word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Submission.BoseGases.q2word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseBoxFix.q3lowWord fc
              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
              (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0)
              (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [W2potB]
  have herr : (1 / 2) * Work.BoseFixR.errKafz v R μ (C₀ + C₁ + C₂ + C₃)
        * Work.BoseBoxFix.normB v μ n Φ
      = ((1 / 2) * Work.BoseFixR.errKafz v R μ C₀ * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ)
        + ((1 / 2) * Work.BoseFixR.errKafz v R μ C₂ * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₃ * Work.BoseBoxFix.normB v μ n Φ) := by
    rw [errKafz_add, errKafz_add, errKafz_add]
    ring
  rw [hwords, herr]
  -- ## the pointwise splitting identity, the integral split, and the arithmetic
  have hsplit := AVgen_potOnly_eq_potGroups
    (B := fun T => boxSlotSum e T)
    (idop := (id : (Xn n → ℂ) → (Xn n → ℂ)))
    (f := (HM μ).f) (g := (HM μ).g) (T_NH := T_NH)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (E := (HonestBoxFam v h fc fu HM μ).E) (gHat0 := 8 * Real.pi * BoseGases.a v)
  have hstep : (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * AVgen (fun T => boxSlotSum e T)
              (id : (Xn n → ℂ) → (Xn n → ℂ)) (HM μ).f (HM μ).g T_NH
              ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
              (potOnlyEnv (HonestBoxFam v h fc fu HM μ).E)
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      = ((∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potContactChem (fun T => boxSlotSum e T)
                  (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
          + (∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potChiLin (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re)
        + ((∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potPairRows (fun T => boxSlotSum e T) (HM μ).f
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
          + (∫ x : Submission.BoseGases.X n,
            star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
              * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                  ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
                  (HonestBoxFam v h fc fu HM μ).E
                  (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re) := by
    rw [hsplit]
    simp only [Pi.add_apply]
    exact integral_re_add4 (n := n) hi0 hi1 hi2 hi3
  rw [hstep]
  linarith [hg0, hg1, hg2, hg3]



theorem PotCubicG_mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin₁ Nmin₂ : ℝ → ℕ} {ε₀ C : ℝ}
    (hle : ∀ μ, Nmin₂ μ ≤ Nmin₁ μ)
    (hP : PotCubicG v h fc fu R J Nmin₂ ε₀ C) :
    PotCubicG v h fc fu R J Nmin₁ ε₀ C := by
  intro HM hN
  exact hP HM (fun μ => le_trans (hle μ) (hN μ))



theorem FormW2BpotG_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (h0 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotContactChem v h fc fu R J Nmin ε₀ C)
    (h1 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotChiLin v h fc fu R J Nmin ε₀ C)
    (h2 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin ε₀ C)
    (h3 : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      PotCubicG v h fc fu R J Nmin ε₀ C) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      FormW2BpotG v h fc fu R J Nmin ε₀ C := by
  obtain ⟨N0, ε0, C0, hε0, hC0, g0⟩ := h0
  obtain ⟨N1, ε1, C1, hε1, hC1, g1⟩ := h1
  obtain ⟨N2, ε2, C2, hε2, hC2, g2⟩ := h2
  obtain ⟨N3, ε3, C3, hε3, hC3, g3⟩ := h3
  let N : ℝ → ℕ := fun μ => max (max (N0 μ) (N1 μ)) (max (N2 μ) (N3 μ))
  have hN0 : ∀ μ, N0 μ ≤ N μ := fun μ => le_trans (le_max_left _ _) (le_max_left _ _)
  have hN1 : ∀ μ, N1 μ ≤ N μ := fun μ => le_trans (le_max_right _ _) (le_max_left _ _)
  have hN2 : ∀ μ, N2 μ ≤ N μ := fun μ => le_trans (le_max_left _ _) (le_max_right _ _)
  have hN3 : ∀ μ, N3 μ ≤ N μ := fun μ => le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨N, ?_⟩
  exact FormW2BpotG_of_potGroups v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 N
      ⟨ε0, C0, hε0, hC0, PotContactChem_mono hN0 g0⟩
      ⟨ε1, C1, hε1, hC1, PotChiLin_mono hN1 g1⟩
      ⟨ε2, C2, hε2, hC2, PotPairRows_mono hN2 g2⟩
      ⟨ε3, C3, hε3, hC3, PotCubicG_mono hN3 g3⟩
      (fun {ε₀} => Work.BoseBoxFock.PotGroupsIntegrable_holds v h hv hv1 hvrad hR hv_supp hav
        fc fu J hB3 N ε₀)



theorem RowB_of_kin4_potG (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ)
    (hkin : ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      FormRowKin4 v h fc fu R J Nmin ε₀ C)
    (hpot : ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      FormW2BpotG v h fc fu R J Nmin ε₀ C) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.RowB v h fc fu R J Nmin ε₀ C := by
  obtain ⟨εk, Ck, hεk, hCk, hK⟩ := hkin
  obtain ⟨εp, Cp, hεp, hCp, hP⟩ := hpot
  obtain ⟨Cb, εb, hCb, hεb, hbf⟩ := bf3a_pot v h hv hv1 hvrad hR hv_supp hav fc hB3
  obtain ⟨εe, Ce, hεe, hCe, herr⟩ := err_arith hav hR
  refine ⟨min (min εk εp) (min εb εe), (Ck + Cp) / 2 + Cb * Ce, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hεk hεp) (lt_min hεb hεe)
  · nlinarith [hCk, hCp, hCb, hCe]
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  -- ## the threshold instances of the four inputs (`Adm` is monotone in its threshold)
  have hε : μ * (BoseGases.a v) ^ 3 ≤ min (min εk εp) (min εb εe) := hAdm.2.1
  have hAdm_k : Work.BoseBoxFix.Adm v εk μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_left _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm_p : Work.BoseBoxFix.Adm v εp μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hAdm_b : Work.BoseBoxFix.Adm v εb μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm_e : Work.BoseBoxFix.Adm v εe μ :=
    ⟨hAdm.1, le_trans hε (le_trans (min_le_right _ _) (min_le_right _ _)), hAdm.2.2⟩
  -- ## the four inputs at this state
  have hK' := hK HM hNmin μ hAdm_k hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    T_NH hT
  have hP' := hP HM hNmin μ hAdm_p hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    T_NH hT
  have hbfa := hbf μ hAdm_b n Φ hn
  have herrB : Work.BoseBoxFock.errB v R μ ≤ Work.BoseFixR.errKafz v R μ Ce :=
    (herr μ hAdm_e J hJ).1
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := le_of_lt hnorm
  -- ## the box restriction is a good, box-supported state
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hAdm.1 hav
  obtain ⟨hΘcm, hΘcb, hΘsupp, -, hmassC⟩ := Work.BoseBoxFock.boxRestrictState hℓ Φ
  have hGoodΨ : SlotGood (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) :=
    ⟨hΘcm, hΘcb⟩
  -- ## the pointwise isolation of the two groups
  have hsplit := Work.BoseBoxFock.AVgen_split_kin_pot (n := n)
    (B := fun T => Work.BoseDict.boxSlotSum e T)
    (idop := (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)))
    (f := (HM μ).f) (g := (HM μ).g) (T_NH := T_NH)
    (PHs := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (gHat0 := 8 * Real.pi * BoseGases.a v)
  -- ## `AVgen` preserves good states in both groups
  have hRowK : RowGood
      (AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
        (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0) :=
    rowGood_AVgen (n := n) h1 h2 h3 (HM μ).f (HM μ).g T_NH
      (∅ : Finset (Lab (HM μ).N))
      (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
  have hRowP : RowGood
      (AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        (HM μ).f (HM μ).g T_NH
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (8 * Real.pi * BoseGases.a v)) :=
    rowGood_AVgen (n := n) h1 h2 h3 (HM μ).f (HM μ).g T_NH
      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (8 * Real.pi * BoseGases.a v)
  -- ## integrability of the two group integrands
  have hi1 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
        * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
            (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x) :=
    Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hRowK (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).1
      (hRowK (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).2
  have hi2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
        * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
            (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
            (8 * Real.pi * BoseGases.a v)
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x) :=
    Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hRowP (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).1
      (hRowP (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).2
  -- ## the pointwise split of the left-hand integrand
  have hpt : (fun x : Submission.BoseGases.X n =>
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x)
      = fun x =>
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x
          + star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x := by
    funext x
    rw [hsplit]
    simp only [Pi.add_apply, mul_add]
  -- ## the split of the real part of the Bochner integral
  have hkey : (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      = (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
        + (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re := by
    rw [hpt, MeasureTheory.integral_add hi1 hi2, Complex.add_re]
  -- ## `massR` of the box restriction is the box norm
  have hFold : (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)
      * (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v))).indicator
          (fun _ => (1 : ℝ)) x)
      = boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ := rfl
  have hmass : Work.BoseBoxFock.massR
      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [← hFold, hmassC]
    rfl
  -- ## `wordB` splits into its kinetic, chemical and pair parts
  have hword := Work.BoseBoxFock.wordB_eq_kin_add_chemPair v h hv1 hvrad hR hv_supp hAdm.1 hav
    (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff.continuous
  -- ## the error linearity
  have hekadd : ∀ a b : ℝ, Work.BoseFixR.errKafz v R μ (a + b)
      = Work.BoseFixR.errKafz v R μ a + Work.BoseFixR.errKafz v R μ b := by
    intro a b
    simp only [Work.BoseFixR.errKafz]
    ring
  have hErrsplit : Work.BoseFixR.errKafz v R μ ((Ck + Cp) / 2 + Cb * Ce)
      = (Work.BoseFixR.errKafz v R μ Ck + Work.BoseFixR.errKafz v R μ Cp) / 2
        + Work.BoseFixR.errKafz v R μ (Cb * Ce) := by
    rw [hekadd ((Ck + Cp) / 2) (Cb * Ce), errKafz_div_two]
  -- ## `bf3a_pot`, with its error absorbed by `errKafz (Cb * Ce)`
  have hW2p : Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h)
            (Work.BoseBox.sideAt μ (BoseGases.a v)) μ (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
          + ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) *
              (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)
                + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT *
                    ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                      * Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-2 : ℤ)
                  * Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                      (Φ : Submission.BoseGases.X n → ℝ))
          + Work.BoseFixR.errKafz v R μ (Cb * Ce) * Work.BoseBoxFix.normB v μ n Φ := by
    have hCB : Cb * Work.BoseBoxFock.errB v R μ ≤ Work.BoseFixR.errKafz v R μ (Cb * Ce) := by
      have h := mul_le_mul_of_nonneg_left herrB hCb
      rwa [show Cb * Work.BoseFixR.errKafz v R μ Ce
            = Work.BoseFixR.errKafz v R μ (Cb * Ce) by
          simp only [Work.BoseFixR.errKafz]; ring] at h
    have h2 : Cb * Work.BoseBoxFock.errB v R μ * Work.BoseBoxFix.normB v μ n Φ
        ≤ Work.BoseFixR.errKafz v R μ (Cb * Ce) * Work.BoseBoxFix.normB v μ n Φ :=
      mul_le_mul_of_nonneg_right hCB hnorm0
    linarith [hbfa, h2]
  -- ## the two halves, added
  have hstep : (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
        + (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      ≤ (Work.BoseBoxFix.wordB v h μ n Φ
          + Work.BoseFixR.errKafz v R μ ((Ck + Cp) / 2 + Cb * Ce)
            * Work.BoseBoxFix.normB v μ n Φ) := by
    have hmiddle : (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
        + (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
        ≤ (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
            + Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (BoseGases.a v)) μ (Φ : Submission.BoseGases.X n → ℝ)
            + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ))
          + ((1 / 2) * Work.BoseFixR.errKafz v R μ Ck * Work.BoseBoxFix.normB v μ n Φ
              + (1 / 2) * Work.BoseFixR.errKafz v R μ Cp * Work.BoseBoxFix.normB v μ n Φ
              + Work.BoseFixR.errKafz v R μ (Cb * Ce) * Work.BoseBoxFix.normB v μ n Φ) := by
      linarith [hK', hP', hW2p]
    have heq : ((1 / 2) * Work.BoseFixR.errKafz v R μ Ck * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ Cp * Work.BoseBoxFix.normB v μ n Φ
          + Work.BoseFixR.errKafz v R μ (Cb * Ce) * Work.BoseBoxFix.normB v μ n Φ)
        = Work.BoseFixR.errKafz v R μ ((Ck + Cp) / 2 + Cb * Ce)
            * Work.BoseBoxFix.normB v μ n Φ := by
      rw [hErrsplit]
      ring
    linarith [hmiddle, heq, hword]
  -- ## the final bookkeeping
  have hfin : (Work.BoseBoxFix.wordB v h μ n Φ
        + Work.BoseFixR.errKafz v R μ ((Ck + Cp) / 2 + Cb * Ce)
          * Work.BoseBoxFix.normB v μ n Φ)
      = (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
          + Work.BoseFixR.errKafz v R μ ((Ck + Cp) / 2 + Cb * Ce))
        * Work.BoseBoxFock.massR
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) := by
    rw [hmass]
    field_simp [ne_of_gt hnorm]
  rw [hkey]
  exact le_trans hstep hfin.le


theorem oneBody_kinGroup_le4 {Kτ Kη : ℝ} (hKτ : 0 ≤ Kτ) (hKη : 0 ≤ Kη)
    (hτ : ∀ {ℓ s d eT : ℝ}, 0 < ℓ → 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 →
      ∀ (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
          + Kτ * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hη : ∀ {ℓ d κ : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 → (d ^ 2 * ℓ)⁻¹ ≤ κ →
      ∀ (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
        ≤ 24 * Work.BoseKinLoc.momForm ℓ d 0 ψ + Kη * d ^ 6 * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    {ℓ s d eT b κ : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d) (hd1 : d ≤ 1) (heT : 0 ≤ eT)
    (heT1 : eT ≤ 1) (hb : 0 < b) (hκ : (d ^ 2 * ℓ)⁻¹ ≤ κ)
    (hsb : Kτ * s ≤ b / 20) (hdb : eT * Kη * d ^ 4 ≤ 3)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hgap0 : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ) (hmom0 : 0 ≤ Work.BoseKinLoc.momForm ℓ d 0 ψ)
    (hneu0 : 0 ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ) :
    (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
      + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
        - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
        - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ) := by
  have h1 := hτ hℓ hs hd hd1 heT heT1 N ψ hψ
  have h2 := hη hℓ hd hd1 hκ fu N ψ hψ
  set G := Work.BoseKinLoc.gapBare ℓ 0 ψ
  set Mo := Work.BoseKinLoc.momForm ℓ d 0 ψ
  set Sτ := (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
  set Sη := (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
  have hfsT : Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
      = Work.BoseKinLoc.neuWord ℓ d eT 0 ψ + b * ℓ ^ (-2 : ℤ) * G
        + b * eT * (d * ℓ) ^ (-2 : ℤ) * Mo + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := rfl
  rw [hfsT]
  have hl2 : ℓ ^ (-2 : ℤ) = (ℓ ^ 2)⁻¹ := by simp [zpow_neg]
  have hdl2 : (d * ℓ) ^ (-2 : ℤ) = (d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹ := by
    rw [zpow_neg, ← mul_inv, ← mul_pow]; norm_cast
  rw [hl2, hdl2]
  have hℓ2 : 0 < (ℓ ^ 2)⁻¹ := by positivity
  have hd2 : 0 < (d ^ 2)⁻¹ := by positivity
  -- η_H row: (eT b /(2 d² ℓ²))(1/32) Sη ≤ (eT b /(d²ℓ²))·(24/64) Mo + b ℓ⁻² (eT Kη d⁴/64) G
  have hηrow : eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * Sη)
      ≤ (3 / 8) * (b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo)
        + b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G := by
    have hc : 0 ≤ eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h2 hc
    have e1 : eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * Sη)
        = eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) * Sη := by ring
    have e2 : eT * b / (2 * d ^ 2 * ℓ ^ 2) * (1 / 32 : ℝ) * (24 * Mo + Kη * d ^ 6 * G)
        = (3 / 8) * (b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo)
          + b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G := by
      field_simp
      ring
    rw [e1]; linarith [this, e2.le, e2.ge]
  have hgapτ : Kτ * s * (ℓ ^ 2)⁻¹ * G ≤ (b / 20) * (ℓ ^ 2)⁻¹ * G := by
    have := mul_le_mul_of_nonneg_right hsb (mul_nonneg hℓ2.le hgap0)
    nlinarith [this]
  have hgapη : b * (ℓ ^ 2)⁻¹ * (eT * Kη * d ^ 4 / 64) * G ≤ (3 / 64 * b) * (ℓ ^ 2)⁻¹ * G := by
    have h16 : eT * Kη * d ^ 4 / 64 ≤ 3 / 64 := by linarith
    have hbg : 0 ≤ b * (ℓ ^ 2)⁻¹ * G := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h16 hbg]
  have hmo : 0 ≤ b * eT * ((d ^ 2)⁻¹ * (ℓ ^ 2)⁻¹) * Mo := by positivity
  have hb2 : b / (2 * ℓ ^ 2) * G = (b / 2) * (ℓ ^ 2)⁻¹ * G := by
    field_simp
  rw [hb2]
  nlinarith [h1, hηrow, hgapτ, hgapη, hmo, hneu0, mul_nonneg hb.le (mul_nonneg hℓ2.le hgap0)]



def OBineq4 (ℓ s d eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (ψ : E3 → ℝ) : Prop :=
    (∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
      + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
        - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
        - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ)



/-! ## v2 PART C — the proved glue of the transfer -/

theorem cnPlus_nonneg' (ℓ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Submission.BoseGases.cnPlus ℓ Φ := by
  unfold Submission.BoseGases.cnPlus
  exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _


theorem cred_nonneg (v : ℝ³ → ℝ) (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4
          - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100)
        * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) := by
  have hb : (Work.BoseBox.paramsAt μ (BoseGases.a v)).b = 1 / 16 := rfl
  have hℓ := Work.BoseBox.sideAt_pos hμ hav
  rw [hb]
  have := cnPlus_nonneg' (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ
  have hz : 0 ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) := zpow_nonneg hℓ.le _
  positivity


/-- `FormRowKin4 ⟹ FormRowKin` (the larger reserve is a stronger statement). PROVED. -/
theorem FormRowKin_of_FormRowKin4 {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < BoseGases.a v)
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin : ℝ → ℕ} {ε₀ C : ℝ}
    (hK : FormRowKin4 v h fc fu R J Nmin ε₀ C) :
    Work.BoseBoxFock.FormRowKin v h fc fu R J Nmin ε₀ C := by
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hk := hK HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hc := cred_nonneg v hav hAdm.1 (n := n) (Φ : Submission.BoseGases.X n → ℝ)
  linarith


/-- **LowBand (re-filed) from the `n₊`-linear bound + its arithmetic** (PROVED; `C = 0`). -/
theorem PotCubicLowBandG_of_nplus {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin : ℝ → ℕ} {ε₀ K : ℝ} (hK : 0 ≤ K)
    (hlin : LowBandNPlusLinear v h fc fu J Nmin ε₀ K) (har : LowBandArith v h fc fu Nmin ε₀ K) :
    PotCubicLowBandG v h fc fu R J Nmin ε₀ 0 := by
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hl := hlin HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have ha := har HM hNmin μ hAdm
  have hc := cnPlus_nonneg' (Work.BoseBox.sideAt μ (BoseGases.a v))
    (Φ : Submission.BoseGases.X n → ℝ)
  have h0 : Work.BoseFixR.errKafz v R μ 0 = 0 := by simp [Work.BoseFixR.errKafz]
  rw [h0]
  have := mul_le_mul_of_nonneg_right ha hc
  nlinarith [this]


end Work.BoseBoxFock.FRK
