import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBogFS.existsAdmRegime
import Submission.Work.BoseBogFS.honestRegimeRows
import Submission.Work.BoseBogFS.honestThresholdRow
import Submission.Work.BoseBoxFock.CloseCondFSCompat
import Submission.Work.BoseBoxFock.RB4boxDomFS_of_bridge
import Submission.Work.BoseFixR.NodeRestrictedBFS
import Submission.Work.BoseRowQ2.GateAll
import Submission.Work.BoseRowQ2.KzBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AllDefs` — the `All` vocabulary (label-0 row of `Q₂^ex` included)

Design: curric-46, 2026-10-07 (audit §4 item 5).  Every definition below is the
corresponding one of the frozen `BoseBoxFock/Defs.lean` with exactly these changes:

* `F.Q2ex` ↦ `F.Q2exAll` (all χ-labels, `Work.BoseRowQ2.Defs`), `KzOpFS` ↦ `KzOpFSAll`,
  `valFS` ↦ `valFSAll` (`KzAll.lean`);
* `Q3KernelFSAll.q2exLowerR` carries the window `T.NWindow E.bigM Ψ` (its only consumer,
  C3Q `Est1/Assembly`, applies it at a window state);
* the gate conjunct of `RViewFSAll` is `Q3KernelFSAll`; **every other conjunct is
  verbatim, in the same order**, so positional destructuring of `RViewFS` ports by renaming.

Field names of `Q3KernelFSAll` are those of `Q3KernelFS`, so dot-access ports by renaming.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The §10 gate, `All` form.**  `Q3KernelFS` with `q2exLowerR` against `Q2exAll` and
restricted to the `𝓜`-window. -/
structure Q3KernelFSAll {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp2 : ∀ s, E.fL s ≠ 0 → ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
  kmom_subW : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.kmom (s - k) = F.kmom s - F.kmom k
  kmom_subL : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → F.kmom (s - s') = F.kmom s - F.kmom s'
  hasKernelW : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → E.W1 j ≠ 0 →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hasKernel_noWrap : ∀ i j, Work.BoseK15.NoWrap F.kmom i j →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * Work.BoseB7A.eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * Work.BoseB7A.eta E
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s) ∧
      ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat
  alpha_lip : ∀ p q, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  /-- **The corrected row** (`Q2exAll`, windowed). -/
  q2exLowerR : ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
    2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2exAll E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)
        + (1 / 2) * F.qw Ψ (F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k))

/-- **The corrected view, `All` form**: `RViewFS` verbatim, gate conjunct `Q3KernelFSAll`. -/
def RViewFSAll {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : Prop :=
  Nonempty (Work.BoseB7.FSParamsView E) ∧ E.mu = μ ∧ E.aScat = a v
    ∧ E.ell = ell v μ ∧ E.bigM = bigM (paramsAt μ (a v)) (a v) μ
    ∧ E.b = (paramsAt μ (a v)).b ∧ E.d = (paramsAt μ (a v)).d
    ∧ E.s = (paramsAt μ (a v)).s ∧ E.eT = (paramsAt μ (a v)).eT
    ∧ E.intM = (paramsAt μ (a v)).M ∧ gHat0 = 8 * π * a v
    ∧ E.tau = (fun k => tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
        (paramsAt μ (a v)).d (ell v μ) (F.kmom k))
    ∧ E.A = (fun k => E.tau k + E.rho * E.W1 k)
    ∧ E.B = (fun k => E.rho * E.W1 k)
    ∧ (∃ (fu : LowCut) (Λ : ℝ), 4 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ Λ ∧
        E.W1 = (fun k => uvCut fu Λ (F.kmom k) * chat (W1fun v h (ell v μ)) (F.kmom k)))
    ∧ E.W1omega = (fun k => chat (W1omegaFun v h (ell v μ)) (F.kmom k))
    ∧ E.W1omega0 = chat (W1omegaFun v h (ell v μ)) 0
    ∧ E.hatChi = (fun k => chat (chiFun (ell v μ)) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ E.hatChiSq = (fun k =>
        chat (fun z => chiFun (ell v μ) z ^ 2) (F.kmom k)
          / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ (∃ fc : LowCut, E.fL = (fun k => fLFS fc E.KL E.mu E.aScat (F.kmom k)))
    ∧ (∃ fu : LowCut, T.NH = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
        etaH fu (E.KL * Real.sqrt (E.mu * E.aScat)) (F.kmom k) • F.nOp k)
    ∧ (∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧
        ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b
        ∧ ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFSAll K₀ F T (KzEnvAt E ρ))

def _root_.Work.BoseFixR.KzDatum.viewFSAll (D : KzDatum) (v : ℝ³ → ℝ) (h : ScatSol v)
    (μ : ℝ) : Prop :=
  RViewFSAll v h μ D.F D.T D.E D.gHat0

/-- FS §8 at the honest model, `valFSAll`. -/
def RB4boxDomAtAll (v : ℝ³ → ℝ) (h : ScatSol v) (R J : ℝ) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        (n : ℝ) ≤ 2 * μ * sideAt μ (a v) ^ 3 →
        IsLowB v h J μ n Φ →
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
        (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 * normB v μ n Φ)
          ≤ wordB v h μ n Φ + errKafz v R μ C * normB v μ n Φ

def RB4boxDomFSAll (v : ℝ³ → ℝ) (h : ScatSol v) (R J : ℝ) (fc fu : LowCut) : Prop :=
  ∃ Nmin : ℝ → ℕ, ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) →
    RB4boxDomAtAll v h R J fc fu HM

/-- FS §9, **far-leg target** (premise `viewFSAll`, conclusion still at `KzOpFS`). -/
def RB5FSAllK (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → FarCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      FarBound v μ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOpFS (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- FS §9 at a family, `All` vocabulary. -/
def RB5FSAll (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → FarCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      FarBound v μ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOpFSAll (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- FS §10+§11 close case, `All` vocabulary. -/
def RB67FSAll (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      CloseBoundR v R μ C ρ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOpFSAll (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- `eq:Combined1`, premise `viewFSAll` (body verbatim from `BogOpBoundFS`). -/
def BogOpBoundFSAll (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ) (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0) * (D μ).F.normSq f

/-- `thm:Control3Q`'s word, `Q2exAll`. -/
def controlWordHiAll {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.dNumOpR E (RHi F E) + T.Q3T E + F.Q2exAll E + T.linOpT E + (E.b / 50) • T.gapOpT E

def Control3QFSAll (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * Work.BoseB7A.controlErrA E) * F.normSq Φ ≤ F.qw Φ (controlWordHiAll T E)

def HonestGateAtFSAll (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (ε₀ K₀ b₀ : ℝ) : Prop :=
  0 ≤ K₀ ∧ 0 < b₀ ∧
    (∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b) ∧
    (∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      Q3KernelFSAll K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
        (KzEnvAt (HonestBoxFam v h fc fu HM μ).E ρ))

def HonestGateFSAll (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut) (K₀ b₀ : ℝ) : Prop :=
  ∃ (Ng : ℝ → ℕ) (εg : ℝ), 0 < εg ∧ εg ≤ 1 ∧
    ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Ng μ ≤ (HM μ).N) →
      HonestGateAtFSAll v h fc fu HM εg K₀ b₀


/-- The far leg delivers `RB5FSAllK`; the label-0 row is a nonnegative form
(`kz0Coef = 2ρŴ₁ω(0) ≥ 0`: `kmom 0 = 0` from `F.kmom_neg`, `W1omega0_nonneg` from the
gate at `ρ = μ`, `closeCondFS_self`). -/
theorem RB5FSAll_of_K {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} {D : ℝ → KzDatum}
    (hav : 0 < BoseGases.a v) (hK : RB5FSAllK v h R D) : RB5FSAll v h R D := by
  obtain ⟨ε₀, hε₀, H⟩ := hK
  refine ⟨ε₀, hε₀, fun μ hAdm hview ρ hρ hfar f hf => le_trans (H μ hAdm hview ρ hρ hfar f hf)
    (KzOpFS_qw_le_KzOpFSAll _ _ _ _ _ ?_ f)⟩
  have hμ : 0 < μ := hAdm.1
  have hv := hview
  unfold KzDatum.viewFSAll RViewFSAll at hv
  obtain ⟨-, -, -, hell, -, -, -, -, -, -, -, -, -, -, -, hWo, hWo0, -, -, -, -, -,
    K₀, b₀, -, -, -, hgate⟩ := hv
  have hW0 : 0 ≤ (D μ).E.W1omega0 :=
    (hgate μ (Work.BoseBoxFock.closeCondFS_self hμ hav)).W1omega0_nonneg
  have hk0 : (D μ).F.kmom 0 = 0 := by
    have h0 := (D μ).F.kmom_neg 0
    rw [neg_zero] at h0
    have h2 : (2 : ℝ) • (D μ).F.kmom 0 = 0 := by rw [two_smul]; nth_rewrite 1 [h0]; simp
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hWeq : (D μ).E.W1omega 0 = (D μ).E.W1omega0 := by rw [hWo, hWo0]; simp only [hk0]
  have hℓ : 0 < (D μ).E.ell := by rw [hell]; exact Work.BoseBox.sideAt_pos hμ hav
  have hr : 0 ≤ (KzEnvAt (D μ).E ρ).rho := by
    rw [Work.BoseRowQ2.kzEnvAt_rho_of_nonneg hρ hℓ]; exact hρ
  unfold kz0Coef
  show 0 ≤ (KzEnvAt (D μ).E ρ).rho * ((D μ).E.W1omega 0 + (D μ).E.W1omega0)
  rw [hWeq]
  exact mul_nonneg hr (by linarith)

end Work.BoseBoxFock
