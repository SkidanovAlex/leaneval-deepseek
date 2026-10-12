import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseAllGlue.AllAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.RB67FSAll_of_pieces` — FS §10+§11 close case, `All` vocabulary

Design item 5 glue (D3), row 2: the `All`-vocabulary port of
`Work.BoseBoxFock.RB67FS_of_pieces` (`BoseBoxFock/RB67FS_of_pieces.lean`).

The residual `RB67FSAll` at the honest box family, from the three `All` pieces FS use:

* `hgate : HonestGateAtFSAll v h fc fu HM εg K₀ b₀` — the §10 gate *at the honest family*,
  with `Q3KernelFSAll` for every close density;
* `hctrl : Control3QFSAll K₀ b₀ hb₀` — FS `thm:Control3Q` at the corrected `Q2exAll` row
  (this is the design's item 5 row `control3QFSAll`, which is *taken as a hypothesis* here
  until the C3Q port `BoseB7AK/C3QAll/` lands; nothing below uses its internals);
* `hbog : BogOpBoundFSAll v h R (HonestBoxFam …)` — FS `thm:BogHamDiag` + `lem:BogIntegral`
  in the combined `eq:Combined1` form.

The argument is FS §11 and it is the original's *word for word*: the decomposition
`KzOpFSAll_decomp` (`Work.BoseAllGlue.AllAPI`, the `All` form of `eq:SimplifyKz`), the two
hypotheses at the close data, and the slot bookkeeping.  The one place where the corrected
close threshold matters is the χ-mode number term `(ρ−μ)Ŵ₁(0)·Σ_k a_k†a_k`, absorbed by the
remaining gap `(b/2 − b/50)·gapOpT` (`num_term_pays`).

The only instrument that changes is the `qw`-form of the decomposition: the label-`0` row of
`Q₂^ex` sits in `controlWordHiAll` (the same operator difference by which `KzOpFSAll` differs
from `KzOpFS`), so it cancels against the added row exactly as in `KzOpFS`'s own decomposition
(`Work.BoseRowQ2.KzOpFSAll_eq_KzOpFS_add_sub`).

The statement is copied from `Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` (item 5 glue).
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
set_option maxHeartbeats 4000000

/-! ## 1. FS §11's close-case estimate at one parameter point, `All` vocabulary -/

/-- **FS §11's close-case estimate at one parameter point, `All` vocabulary.**  Everything the
argument consumes is an explicit hypothesis: the `All` view `RViewFSAll`, the combined
Bogoliubov input `hbog_at` (FS `eq:Combined1` at the level of `KzBogFS`, which is *not*
`All`-dependent), the `Control3QFSAll` input `hctrl_at` (FS `thm:Control3Q`), the gate `hKK`
(at `Q3KernelFSAll`) and the gap tie `hb0E`.  This is the form in which `RB67FSAll_of_pieces`
applies it at the honest family. -/
theorem RB67FSAll_close_step {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hR : 0 < R) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (g0 : ℝ)
    {μ ε₀ t₀ Cb Cc : ℝ} {K₀ b₀ : ℝ} (hCc : 0 ≤ Cc)
    (hAdm : Adm v ε₀ μ) (hε₀_le_t : ε₀ ≤ t₀) (hε₀_le_1 : ε₀ ≤ 1)
    (hεR : ε₀ ≤ (a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
    (hεh : ε₀ ≤ (1 / 2 : ℝ) ^ (323 / 3 : ℝ))
    (hview : RViewFSAll v h μ F T E g0)
    (hbog_at : ∀ (ρ : ℝ), 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f : F.H, T.NWindow E.bigM f →
      (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
        - Cb * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
            * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ)) * F.normSq f
      + F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
    ≤ F.qw f (KzBogFS F E ρ)
      + ((1 / 2) * ρ ^ 2 * E.ell ^ 3 * E.W1omega0 + (1 / 2) * (ρ - E.mu) ^ 2 * E.ell ^ 3 * g0)
          * F.normSq f)
    (hctrl_at : ∀ {Mode' : Type} [AddCommGroup Mode'] [Fintype Mode'] [DecidableEq Mode']
      (F' : Work.BoseB7.FockData.{0, 0} Mode') (T' : Work.BoseB7A.TildeData F') (E' : Work.BoseB7.Q3Env Mode')
      (hv' : Work.BoseB7.FSParamsView E'), hv'.t ≤ t₀ → b₀ ≤ E'.b → Q3KernelFSAll K₀ F' T' E' →
        ∀ Φ : F'.H, T'.NWindow E'.bigM Φ →
          -(Cc * Work.BoseB7A.controlErrA E') * F'.normSq Φ ≤ F'.qw Φ (controlWordHiAll T' E'))
    (hb0E : b₀ ≤ E.b)
    (hKK : ∀ (ρ : ℝ), CloseCondFS v μ ρ → Q3KernelFSAll K₀ F T (KzEnvAt E ρ)) :
    ∀ (ρ : ℝ), 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f : F.H, T.NWindow E.bigM f →
      CloseBoundR v R μ (Cb + Cc) ρ * F.normSq f ≤ F.qw f (KzOpFSAll F T E g0 ρ) := by
  intro ρ hρ hclose f hwin
  obtain ⟨hFSPne, hmu, haSc, hell, hbigM, hb, hd, hs, heT, hintM, hg0, htau, hA, hB, hW1,
    hW1o, hW1o0, hchi, hchiSq, hfL, hNH, hBessel, hgateview⟩ := hview
  have hFSP : Work.BoseB7.FSParamsView E := hFSPne.some
  -- ## 0. the smallness data
  have hμ : 0 < μ := hAdm.1
  have hdilpos : 0 < dil v μ := by rw [dil]; positivity
  have hdil1 : dil v μ ≤ 1 := le_trans hAdm.2.1 hε₀_le_1
  have hRell : R ≤ ell v μ * Submission.BoseGases.chiR0 :=
    adm_R_le_ell_chiR0 hR hav hεR hAdm
  have hhalf : (dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2 := dil_rpow_half hAdm hεh
  have hellpos : 0 < E.ell := Work.BoseB7.ell_pos E hFSP
  have hellne : E.ell ≠ 0 := ne_of_gt hellpos
  have hdne : E.d ≠ 0 := by
    rw [hd, show (paramsAt μ (a v)).d = fsXp (dil v μ) 6 from rfl]
    exact ne_of_gt (fsXp_pos hdilpos)
  have hbval : E.b = 1 / 16 := by rw [hb]; rfl
  have heT0 : 0 ≤ E.eT := by
    rw [heT, show (paramsAt μ (a v)).eT = fsXp (dil v μ) (23 / 4) from rfl]
    exact (fsXp_pos hdilpos).le
  -- ## 1. the close data
  have hρclose : |ρ - E.mu| ≤ E.mu / 2 := by
    rw [hmu]
    refine le_trans hclose ?_
    rw [closeThresholdFS, Work.BoseFixR.Kl_inv_sq v hμ hav]
    have h3 : μ * (dil v μ) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi)
        ≤ μ * (1 / 2) / ((2 : ℝ) ^ 14 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hhalf hμ.le
    have h4 : μ * (1 / 2) / ((2 : ℝ) ^ 14 * Real.pi) ≤ μ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hμ, Real.pi_pos, Real.pi_gt_three]
    linarith
  have hρpos : 0 < ρ := by
    have h2 : -(ρ - E.mu) ≤ |ρ - E.mu| := neg_le_abs _
    rw [hmu] at h2 hρclose
    linarith
  have hE'FSP : Work.BoseB7.FSParamsView (KzEnvAt E ρ) :=
    (FSParamsView_KzEnvAt hFSP hρpos hellne hρclose).some
  -- ## 2. the three hypotheses at `(μ, ρ, f)`
  have hgateK : Q3KernelFSAll K₀ F T (KzEnvAt E ρ) := hKK ρ hclose
  have hbE : b₀ ≤ (KzEnvAt E ρ).b := hb0E
  have ht_le : hE'FSP.t ≤ t₀ := by
    rw [hE'FSP.mu_eq.symm]
    have e1 : (KzEnvAt E ρ).mu = μ := hmu
    have e2 : (KzEnvAt E ρ).aScat = a v := haSc
    rw [e1, e2]
    exact le_trans hAdm.2.1 hε₀_le_t
  have hctrlE : -(Cc * Work.BoseB7A.controlErrA (KzEnvAt E ρ)) * F.normSq f
      ≤ F.qw f (controlWordHiAll T (KzEnvAt E ρ)) :=
    hctrl_at F T (KzEnvAt E ρ) hE'FSP ht_le hbE hgateK f hwin
  -- ## 3. abbreviations
  set n2 : ℝ := F.normSq f with hn2
  set c₀b : ℝ := E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * g0 + (1 / 2) * (ρ - E.mu) ^ 2 * g0
      + (1 / 2) * ρ ^ 2 * E.W1omega0) with hc₀b
  set Mb : ℝ := (1 / 2) * ρ ^ 2 * E.ell ^ 3 * E.W1omega0 with hMb
  set Wb : ℝ := 4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3) with hWb
  set KQ : ℝ := μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
      * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) with hKQ
  set cE : ℝ := Work.BoseB7A.controlErrA (KzEnvAt E ρ) with hcE
  have hn2nn : 0 ≤ n2 := by rw [hn2]; exact F.normSq_nonneg f
  -- ## 4. `hbog` at `(μ, ρ, f)`
  have hbogE : (Wb - Cb * KQ) * n2
      + F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
      ≤ F.qw f (KzBogFS F E ρ) + (Mb + 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3) * n2 := by
    have h1 := hbog_at ρ hρ hclose f hwin
    have e1 : 4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3) = Wb := by
      rw [hWb]
    have e2 : Cb * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
        * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) = Cb * KQ := by
      rw [hKQ]; ring
    have e3 : (1 / 2) * ρ ^ 2 * E.ell ^ 3 * E.W1omega0
        + (1 / 2) * (ρ - E.mu) ^ 2 * E.ell ^ 3 * g0
        = Mb + 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3 := by
      rw [hMb, hg0]; ring
    simp only [e1, e2, e3, ← hn2] at h1
    exact h1
  -- ## 5. the slot estimates
  have hdum : 0 ≤ F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ))) :=
    qw_dNumOpR_nonneg F (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)) (fun k => hgateK.AB k) f
  obtain ⟨Cn, hCn0, hCn16, hBessel'⟩ := hBessel
  have hCn : ∀ g : F.H, F.qw g (∑ k : Mode, F.nOp k) ≤ Cn * F.qw g T.N := fun g => hBessel' g
  have hTN : 0 ≤ F.qw f T.N := qw_TN_nonneg T f
  have hgapge : (KzEnvAt E ρ).ell ^ (-(2 : ℝ)) * F.qw f T.N
      ≤ F.qw f (T.gapOpT (KzEnvAt E ρ)) := qw_gapOpT_ge T (KzEnvAt E ρ) heT0 f
  have hbnonneg : 0 ≤ E.b / 2 - E.b / 50 := by rw [hbval]; norm_num
  have hW10 : |E.W1 0| ≤ 16 * π * a v := by
    obtain ⟨fuW, ΛW, hΛW, hW1eq⟩ := hW1
    have hkm0 : F.kmom 0 = 0 := Work.BoseFixR.kmom_zero F
    have huv : uvCut fuW ΛW (F.kmom 0) = 1 := by
      rw [hkm0, uvCut]
      simpa using fuW.one 0 (by norm_num : (0 : ℝ) ≤ 1)
    rw [hW1eq]
    show |uvCut fuW ΛW (F.kmom 0) * chat (W1fun v h (ell v μ)) (F.kmom 0)| ≤ 16 * π * a v
    rw [huv, one_mul, hkm0]
    exact abs_chat_W1fun_zero_le hR hv hvrad hv_supp (by rw [← hell]; exact hellpos) hRell
  have hℓinv : (KzEnvAt E ρ).ell ^ (-(2 : ℝ))
      = (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) * (μ * a v) := by
    have hμa : 0 < μ * a v := mul_pos hμ hav
    have hKl2 : μ * a v * (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 :=
      Work.BoseFixB1.mu_mul_a_mul_ell_sq μ (a v) hμ hav
    have hellsq : (KzEnvAt E ρ).ell ^ 2 = (sideAt μ (a v)) ^ 2 := by
      rw [show (KzEnvAt E ρ).ell = sideAt μ (a v) from hell]
    have hL : (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 / (μ * a v) := by
      rw [eq_div_iff (ne_of_gt hμa)]
      linarith
    rw [rw_neg_two_eq_inv_sq, rw_neg_two_eq_inv_sq, hellsq, hL, inv_div]
    ring
  have hkey : Cn * |ρ - E.mu| * |E.W1 0|
      ≤ (E.b / 2 - E.b / 50) * (KzEnvAt E ρ).ell ^ (-(2 : ℝ)) := by
    have hnum := num_term_pays (v := v) (μ := μ) (ρ := ρ) (W0 := E.W1 0) (Cn := Cn)
      (ℓ := (KzEnvAt E ρ).ell) (Kl := (paramsAt μ (a v)).Kl) hav hμ hCn0 hCn16 hW10
      hclose hℓinv
    rw [hmu, hbval]
    have hconst : (1 / 16 / 2 - 1 / 16 / 50 : ℝ) = (1 / 2 - 1 / 50) * (1 / 16) := by
      norm_num
    linarith [hnum, hconst]
  have hslot : 0 ≤ ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k)
      + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
    have hSnn : 0 ≤ F.qw f (∑ k : Mode, F.nOp k) := qw_sum_nOp_nonneg F f
    have hSle := hCn f
    have hcoef : -(|ρ - E.mu| * |E.W1 0|) ≤ (ρ - E.mu) * E.W1 0 := by
      have h := neg_abs_le ((ρ - E.mu) * E.W1 0)
      rwa [abs_mul] at h
    have hcoefnn : -(|ρ - E.mu| * |E.W1 0|) ≤ 0 := by
      have h := mul_nonneg (abs_nonneg (ρ - E.mu)) (abs_nonneg (E.W1 0))
      linarith
    have hA : -(|ρ - E.mu| * |E.W1 0|) * F.qw f (∑ k : Mode, F.nOp k)
        ≤ ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k) :=
      mul_le_mul_of_nonneg_right hcoef hSnn
    have hB : -(|ρ - E.mu| * |E.W1 0|) * (Cn * F.qw f T.N)
        ≤ -(|ρ - E.mu| * |E.W1 0|) * F.qw f (∑ k : Mode, F.nOp k) :=
      mul_le_mul_of_nonpos_left hSle hcoefnn
    have hC : -(|ρ - E.mu| * |E.W1 0|) * (Cn * F.qw f T.N)
        = -((Cn * |ρ - E.mu| * |E.W1 0|) * F.qw f T.N) := by ring
    have h1 : -((Cn * |ρ - E.mu| * |E.W1 0|) * F.qw f T.N)
        ≤ ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k) := by
      linarith [hA, hB, hC]
    have h2 : (Cn * |ρ - E.mu| * |E.W1 0|) * F.qw f T.N
        ≤ (E.b / 2 - E.b / 50) * ((KzEnvAt E ρ).ell ^ (-(2 : ℝ)) * F.qw f T.N) := by
      have h4 := mul_le_mul_of_nonneg_right hkey hTN
      linarith [h4]
    have h3 : (E.b / 2 - E.b / 50) * ((KzEnvAt E ρ).ell ^ (-(2 : ℝ)) * F.qw f T.N)
        ≤ (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) :=
      mul_le_mul_of_nonneg_left hgapge hbnonneg
    linarith [h1, h2, h3]
  -- ## 6. the decomposition of `KzOpFSAll`
  have hdec' : F.qw f (KzOpFSAll F T E g0 ρ)
      = c₀b * n2 + F.qw f (KzBogFS F E ρ)
        + ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k)
        + F.qw f (controlWordHiAll T (KzEnvAt E ρ))
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
    rw [Work.BoseAllGlue.qw_KzOpFSAll_eq F T E g0 ρ hellne hdne f, hc₀b, hn2]
  have hstep1 : (Wb - Cb * KQ - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3) * n2
      ≤ F.qw f (KzBogFS F E ρ)
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ))) := by
    linarith [hbogE]
  have hmain : (c₀b - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3 + Wb - Cb * KQ - Cc * cE)
        * n2 ≤ F.qw f (KzOpFSAll F T E g0 ρ) := by
    rw [hdec']
    linarith [hstep1, hctrlE, hslot, hdum]
  -- ## 7. the arithmetic
  have hcE_le : cE ≤ KQ := by
    have hEμ : (KzEnvAt E ρ).mu = μ := hmu
    have hEa : (KzEnvAt E ρ).aScat = a v := haSc
    have hEl : (KzEnvAt E ρ).ell = ell v μ := hell
    have hell3 : E.ell ^ 3 = ell3 v μ := by rw [hell]; rfl
    have hdilE : Work.BoseB7.dil (KzEnvAt E ρ) (1 / 2 + 1 / 323)
        = (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ) := by
      rw [Work.BoseB7.dil, hEμ, hEa]
      rfl
    have hcore : (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ)
        ≤ Real.sqrt (dil v μ) * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ)
            + errExp v μ) := by
      have h1 : (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ)
          = Real.sqrt (dil v μ) * (dil v μ) ^ (1 / 323 : ℝ) := by
        rw [Real.rpow_add hdilpos, Real.sqrt_eq_rpow]
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      have h2 : (dil v μ) ^ (1 / 323 : ℝ) ≤ errExp v μ := by
        rw [errExp]
        exact Real.rpow_le_rpow_of_exponent_ge hdilpos hdil1 (by norm_num)
      linarith [h2, sq_nonneg (fsX v μ),
        mul_nonneg (sq_nonneg (R / a v)) (Real.sqrt_nonneg (dil v μ))]
    have hcEeq : cE = (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ) * (μ ^ 2 * a v * ell3 v μ) := by
      rw [hcE, Work.BoseB7A.controlErrA, Work.BoseB7A.E0, hdilE, hEμ, hEa, hEl,
        show ell3 v μ = ell v μ ^ 3 from rfl]
      ring
    have hKQeq : KQ = (Real.sqrt (dil v μ) * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ)
        + errExp v μ)) * (μ ^ 2 * a v * ell3 v μ) := by
      rw [hKQ]; ring
    rw [hcEeq, hKQeq]
    have hellpos' : 0 < ell v μ := by rw [← hell]; exact hellpos
    have hell3' : 0 < ell3 v μ := by rw [ell3]; exact pow_pos hellpos' 3
    exact mul_le_mul_of_nonneg_right hcore (by positivity)
  have hc0 : c₀b - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3
      = -4 * π * μ ^ 2 * a v * ell3 v μ := by
    rw [hc₀b, hMb, hmu, hg0]
    have hell3 : E.ell ^ 3 = ell3 v μ := by rw [hell]; rfl
    rw [hell3]
    ring
  have hgoal : CloseBoundR v R μ (Cb + Cc) ρ
      ≤ -4 * π * μ ^ 2 * a v * ell3 v μ + Wb - Cb * KQ - Cc * cE := by
    have h3 : CloseBoundR v R μ (Cb + Cc) ρ
        = -4 * π * μ ^ 2 * a v * ell3 v μ + Wb - (Cb + Cc) * KQ := by
      rw [CloseBoundR, hWb, hKQ]
      ring
    rw [h3]
    have h4 : Cc * cE ≤ Cc * KQ := mul_le_mul_of_nonneg_left hcE_le hCc
    linarith
  calc CloseBoundR v R μ (Cb + Cc) ρ * F.normSq f
      = CloseBoundR v R μ (Cb + Cc) ρ * n2 := by rw [hn2]
    _ ≤ (-4 * π * μ ^ 2 * a v * ell3 v μ + Wb - Cb * KQ - Cc * cE) * n2 :=
        mul_le_mul_of_nonneg_right hgoal hn2nn
    _ = (c₀b - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3 + Wb - Cb * KQ - Cc * cE)
        * n2 := by rw [hc0]
    _ ≤ F.qw f (KzOpFSAll F T E g0 ρ) := hmain

/-! ## 2. The close-case residual at the honest family, `All` vocabulary -/

theorem RB67FSAll_of_pieces {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {K₀ b₀ : ℝ}
    (hb₀ : 0 < b₀) {εg : ℝ} (hεg : 0 < εg)
    (hgate : Work.BoseBoxFock.HonestGateAtFSAll v h fc fu HM εg K₀ b₀) (hctrl : Work.BoseBoxFock.Control3QFSAll K₀ b₀ hb₀)
    (hbog : Work.BoseBoxFock.BogOpBoundFSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM)) :
    Work.BoseBoxFock.RB67FSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) := by
  obtain ⟨hK₀nn, hb₀pos, hgate_b, hgate_K⟩ := hgate
  obtain ⟨ε₀b, Cb, hε₀b, hCb, hbog'⟩ := hbog
  obtain ⟨Cc, t₀, hCc, ht₀, hctrl'⟩ := hctrl
  set εR : ℝ := (a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) with hεR
  set εh : ℝ := (1 / 2 : ℝ) ^ (323 / 3 : ℝ) with hεh
  set ε₀ : ℝ := min ε₀b (min εg (min t₀ (min 1 (min εR εh)))) with hε₀
  have hεRpos : 0 < εR := by
    rw [hεR]
    exact Real.rpow_pos_of_pos (div_pos (mul_pos hav Submission.BoseGases.chiR0_pos) hR) _
  have hεhpos : 0 < εh := by rw [hεh]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min hε₀b (lt_min hεg (lt_min ht₀ (lt_min one_pos (lt_min hεRpos hεhpos))))
  obtain ⟨hε₀_le_b, hε₁⟩ :
      ε₀ ≤ ε₀b ∧ ε₀ ≤ min εg (min t₀ (min 1 (min εR εh))) :=
    le_of_le_min (a := ε₀) (by rw [hε₀])
  obtain ⟨hε₀_le_g, hε₂⟩ := le_of_le_min (a := ε₀) hε₁
  obtain ⟨hε₀_le_t, hε₃⟩ := le_of_le_min (a := ε₀) hε₂
  obtain ⟨hε₀_le_1, hε₄⟩ := le_of_le_min (a := ε₀) hε₃
  obtain ⟨hε₀_le_R, hε₀_le_h⟩ := le_of_le_min (a := ε₀) hε₄
  refine ⟨ε₀, Cb + Cc, hε₀pos, by positivity, ?_⟩
  intro μ hAdm hview ρ hρ hclose f hwin
  have hμ0 : 0 < μ := hAdm.1
  have hμ3 : μ * a v ^ 3 ≤ εg := le_trans hAdm.2.1 hε₀_le_g
  have hstep := RB67FSAll_close_step (v := v) (h := h) (R := R)
    (Mode := (HonestBoxFam v h fc fu HM μ).Mode)
    (F := (HonestBoxFam v h fc fu HM μ).F)
    (T := (HonestBoxFam v h fc fu HM μ).T)
    (E := (HonestBoxFam v h fc fu HM μ).E)
    (g0 := (HonestBoxFam v h fc fu HM μ).gHat0)
    (μ := μ) (ε₀ := ε₀) (t₀ := t₀) (Cb := Cb) (Cc := Cc) (K₀ := K₀) (b₀ := b₀)
    hv hR hvrad hv_supp hav hCc hAdm hε₀_le_t hε₀_le_1 hε₀_le_R
    hε₀_le_h hview
    (fun ρ hρ hclose f hwin => hbog' μ (adm_mono hε₀_le_b hAdm) hview ρ hρ hclose f hwin)
    hctrl' (hgate_b μ hμ0 hμ3)
    (fun ρ hclose => hgate_K μ hμ0 hμ3 ρ hclose)
  exact hstep ρ hρ hclose f hwin

end Work.BoseBoxFock

namespace Work.BoseAllGlue

/-- The `Work.BoseAllGlue` name of `Work.BoseBoxFock.RB67FSAll_of_pieces`. -/
alias RB67FSAll_of_pieces := Work.BoseBoxFock.RB67FSAll_of_pieces

end Work.BoseAllGlue
