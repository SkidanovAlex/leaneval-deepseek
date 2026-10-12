import ChallengeDeps
import Submission.Work.BoseBogFS.SharpCap
import Submission.Work.BoseBogFS.ZpMeshLogBound
import Submission.Work.BoseBogFS.fsScaleId_mis
import Submission.Work.BoseBogFS.fsTau_mono_diff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric
open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est Work.BoseBogFS
set_option autoImplicit false

theorem bogOpBoundAtFSWith_of_honestRows (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀1 : ε₀ ≤ 1)
    (Er δ : ℝ → ℝ → ℝ)
    (Dsup G : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f
        ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hZP : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          (bogA (D μ).E ρ k) (bogB (D μ).E ρ k))
        ≤ -(4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0 + Er μ ρ)
    (hKAP : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
          (bogA (D μ).E ρ k) (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
        ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + δ μ ρ))
    (hEzero : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      Er μ ρ ≤ C₄ * errBracket v R μ)
    (hwinG : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      G μ ρ * (winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hδ : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      δ μ ρ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hδ0 : ∀ (μ ρ : ℝ), 0 ≤ δ μ ρ)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.aScat = a v) :
    BogOpBoundAtFSWith v h R D ε₀ := by
  refine ⟨C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1, by positivity, ?_⟩
  intro μ hadm hview ρ hρ hclose f hf
  have hμ : 0 < μ := hadm.1
  have hdil1 : Work.BoseFixR.dil v μ ≤ 1 :=
    le_trans (by simpa only [Work.BoseFixR.dil] using hadm.2.1) hε₀1
  have hcs : CloseCondFS v μ ρ := hclose
  -- the two window facts of the reserve, discharged from the rows (no extra slots needed)
  have hG0 : 0 ≤ G μ ρ :=
    le_trans (sum_RHi_bogD_mul_gammaSq_nonneg (hnum μ hadm hview ρ hclose)) (hG μ ρ)
  have hSpos : 0 < winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ :=
    winKbar_add_zpKapSum_pos (hnum μ hadm hview ρ hclose) (hDsup μ ρ) (hbigM μ hadm hview)
  -- the optimal Cauchy–Schwarz parameter, from the two linear window conditions
  obtain ⟨σ, hσ, hσle⟩ := exists_sigma_reserveLoss_le (D μ).E ρ (Dsup μ ρ) (G μ ρ)
    (C₅ * errBracket v R μ) hG0 hSpos
    (mul_pos hC₅ (errBracket_pos v hμ hav))
    (hwinG μ hadm hview ρ hclose) (hwinGS μ hadm hview ρ hclose)
  have hArith := hArith_of_pieces v R μ ρ (δ μ ρ) (Er μ ρ)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) σ) C₄ C₅ C₀ (D μ).gHat0
    hav hμ hdil1 (hg0 μ hadm hview) hclose (hδ μ hadm hview ρ hclose) hC₀
    (hEzero μ hadm hview ρ hclose) hσle hC₄ hC₅.le
  have hmain := bogOpBound_at v h R (D μ) μ ρ (hnum μ hadm hview ρ hclose) (hmu μ hadm hview)
    (hell μ hadm hview) (Er μ ρ)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) σ) (δ μ ρ)
    (C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1) (hδ0 μ ρ)
    (hZP μ hadm hview ρ hclose) (hKAP μ hadm hview ρ hclose)
    (by
      have hKbar : ∀ g : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM g →
          (D μ).F.qw g (KzBogFS (D μ).F (D μ).E ρ)
            ≤ winKbar (D μ).E (Dsup μ ρ) * (D μ).F.normSq g :=
        fun g hg => qw_KzBogFS_le_window_direct (D μ).F (D μ).T (D μ).E ρ Cn (A μ ρ) (C μ ρ)
          (winKbar (D μ).E (Dsup μ ρ)) (hnum μ hadm hview ρ hclose) (hbigM μ hadm hview)
          (hBessel μ hadm hview) hCn (hAwin μ hadm hview ρ hclose) (hCwin μ hadm hview ρ hclose)
          (hKbig μ hadm hview ρ hclose) g hg
      simpa only [reserveLoss, zpKapSum] using
        qw_dNumOpR_le_res (D μ).F (D μ).T (D μ).E ρ (winKbar (D μ).E (Dsup μ ρ)) (G μ ρ) σ hσ
          (hnum μ hadm hview ρ hclose) hKbar (hG μ ρ))
    hArith f hf
  simpa only [errBracket, mul_assoc, hell μ hadm hview, ell3] using hmain

end Work.BoseBogFS
