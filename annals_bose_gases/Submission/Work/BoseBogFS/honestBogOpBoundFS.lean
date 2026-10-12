import ChallengeDeps
import Submission.Work.BoseBogFS.honestDelta_le
import Submission.Work.BoseBogFS.honestKAP_final
import Submission.Work.BoseBogFS.honestMeshRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestBogOpBoundFS` — `BogOpBoundFS` at the honest family

This is the target of node `BOG`: `Work.BoseBoxFock.BogOpBoundFS v h R (HonestBoxFam v h fc fu HM)`
— the `hbog` hypothesis of `Work.BoseBoxFock.RB67FS_of_pieces` — assembled from

* `Work.BoseBogFS.honestKAP_final` (the `𝒞`-slot, **proved**; its `δ` is discharged here by the
  proved `Work.BoseBogFS.honestDelta_le` / `Work.BoseBogFS.honestDelta_nonneg`, with
  `C₀ := 4·(2C + 8192)`),
* the `hZP`-slot, a hypothesis of `honestBogOpBoundFS_of_rows` (it can be produced by
  `Work.BoseBogFS.honestHZP_of_matchEnv` from the envelope datum and the ZP rows),
* the mechanical window/gate/numeric rows of the capstone
  (`Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows`),

via `bogOpBoundAtFSWith_of_honestRows ∘ BogOpBoundAtFS_of_with ∘
canonical_of_bogOpBoundAtFS` (`BogOpBoundAtFS_iff_canonical` is `Iff.rfl`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`K_ℓ ≥ 1`** at an admissible chemical potential: `K_ℓ = (μ·a³)^{−3/646}` and
`0 < μ·a³ ≤ ε₀ ≤ 1`. -/
theorem one_le_Kl_of_adm {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (hε₀1 : ε₀ ≤ 1)
    (hav : 0 < _root_.BoseGases.a v) (hadm : Adm v ε₀ μ) :
    1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by
  have hKleq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 646) : ℝ) := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    norm_num
  rw [hKleq]
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ (by norm_num)
  · exact mul_pos hadm.1 (pow_pos hav 3)
  · linarith [hadm.2.1, hε₀1]

/-- **`BogOpBoundFS` at the honest family, from the capstone's rows and the `hZP` slot.**
The `𝒞`-slot is `Work.BoseBogFS.honestKAP_final` (proved), and the two `δ`-rows of the capstone are
discharged by `Work.BoseBogFS.honestDelta_le` / `honestDelta_nonneg` with `C₀ = 4(2C + 8192)`. -/
theorem honestBogOpBoundFS_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    (ε₀ R r₁ C Cn C₄ C₅ : ℝ) (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (Er : ℝ → ℝ → ℝ) (Dsup G : ℝ → ℝ → ℝ) (Aa Cc : ℝ → ℝ → ℝ)
    (hav : 0 < _root_.BoseGases.a v) (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅)
    (hCn : Cn ≤ 16)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hnum : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → BogNumeric (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)
    (hbigM : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
    (hBessel : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H,
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
          ((∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) f) f
        ≤ Cn * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N f) f)
    (hAwin : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k ≤ Aa μ ρ)
    (hCwin : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      |bogC (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k| ≤ Cc μ ρ)
    (hKbig : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ →
      10 ^ 6 * (Aa μ ρ + Cc μ ρ + 1) * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM + 1)
        * ((Fintype.card (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode : ℝ) + 1)
        ≤ winKbar (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E (Dsup μ ρ))
    (hDsup : ∀ μ ρ : ℝ,
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      bogD (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ μ ρ : ℝ,
      (∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode).filter
        (RHi (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
        (bogD (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
          * (bogGamma (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hZP : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ →
      (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
          (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            (bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (bogB (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k))
        ≤ -(4 * π * lhyC * ρ ^ 2 * (_root_.BoseGases.a v) * ell3 v μ
              * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
          + Er μ ρ)
    (hEzero : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → Er μ ρ ≤ C₄ * errBracket v R μ)
    (hwinG : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ →
      G μ ρ * (winKbar (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E (Dsup μ ρ)
          + zpKapSum (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 = 8 * π * _root_.BoseGases.a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat = _root_.BoseGases.a v)
    -- the honest `𝒞`-slot rows
    (hRℓ : ∀ μ : ℝ, Adm v ε₀ μ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : ∀ μ : ℝ, Adm v ε₀ μ → R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁)
    (hcond : ∀ μ : ℝ, Adm v ε₀ μ →
      C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 4)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → honestDD v μ R ≤ 1 / 2)
    (hin : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
            ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N →
          R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2
            ≤ honestDD v μ R)
    (hout : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N
            < ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ →
          128 * π * (_root_.BoseGases.a v) * μ
            ≤ (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
              * (max 0 (‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
                  - ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
                    * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹)) ^ 2) :
    Work.BoseBoxFock.BogOpBoundFS v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) := by
  -- the two `δ`-rows of the capstone, supplied internally at `δ := honestDelta v · R C ·`
  have hδ : ∀ μ : ℝ, Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ →
      honestDelta v μ R C ρ ≤ 4 * (2 * C + 8192) * dil v μ * (R / _root_.BoseGases.a v) ^ 2 := by
    intro μ hadm _hview _ρ _hclose
    exact honestDelta_le hav (le_of_lt hadm.1) hC (le_of_lt hR) (one_le_Kl_of_adm hε₀1 hav hadm)
  have hδ0 : ∀ μ ρ : ℝ, 0 ≤ honestDelta v μ R C ρ := fun μ ρ =>
    honestDelta_nonneg (v := v) (R := R) (C := C) (μ := μ) (ρ := ρ) hC (le_of_lt hav)
  refine canonical_of_bogOpBoundAtFS
    (BogOpBoundAtFS_of_with hε₀0 (bogOpBoundAtFSWith_of_honestRows v h R
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) ε₀ hε₀1 Er
      (fun μ ρ => honestDelta v μ R C ρ) Dsup G Cn C₄ C₅ (4 * (2 * C + 8192))
      hav hC₄ hC₅ (by positivity) hCn
      hnum hbigM hBessel Aa Cc hAwin hCwin hKbig hDsup hG
      hZP
      (fun μ hadm hview ρ hclose => by
        have h := honestKAP_final (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
          (R := R) (r₁ := r₁) (C := C) (ε₀ := ε₀)
          hR hv hvrad hv_supp hC hr₁ hT hε₀1 hav hRℓ hreg hcond hδD1 hin hout
          μ hadm hview ρ hclose
        exact h)
      hEzero hwinG hwinGS
      (fun μ hadm hview ρ hclose => hδ μ hadm hview ρ hclose)
      hδ0 hg0 hmu hell hascat))

end Work.BoseBogFS
