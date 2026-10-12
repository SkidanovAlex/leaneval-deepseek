import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/RB67FS_of_pieces.lean` — FS §10+§11 close case at the honest family

The residual `RB67FS` at the honest box family, from the three pieces FS use:

* `hgate : HonestGateAtFS v h fc fu HM εg K₀ b₀` — the §10 gate *at the honest family*:
  `b₀ ≤ E.b` and `Q3KernelFS K₀ F T (KzEnvAt E ρ)` for every close density (this is exactly the
  two ties `Control3QFS` consumes, cf. `RB67CanonOfPiecesV2_FINDING.md` §2);
* `hctrl : Control3QFS K₀ b₀ hb₀` — FS `thm:Control3Q`;
* `hbog : BogOpBoundFS v h R (HonestBoxFam v h fc fu HM)` — FS `thm:BogHamDiag` + `lem:BogIntegral`
  in the combined `eq:Combined1` form of `Defs.lean` (§7).

The argument is FS §11: the `eq:SimplifyKz` decomposition of `KzOpFS` (`KzOpFS_decomp`), the two
hypotheses at the close data, and the bookkeeping of the slots.  The one place where the
corrected close threshold `closeThresholdFS` matters is the χ-mode number term
`(ρ−μ)Ŵ₁(0)·Σ_k a_k†a_k`: its coefficient has no sign, so it is *absorbed by the remaining gap*
`(b/2 − b/50)·gapOpT` (design `F9`),

  `Cn·|ρ−μ|·|Ŵ₁(0)| ≤ (b/2 − b/50)·ℓ⁻²`   (`num_term_pays`),

a pure universal-constant comparison: with `Cn ≤ 16`, `|Ŵ₁(0)| ≤ 16πa v`,
`|ρ−μ| ≤ μK_ℓ⁻²/(2¹⁴π)` (`CloseCondFS`) and `ℓ⁻² = μ·a·K_ℓ⁻²` (`mu_mul_a_mul_ell_sq`), both
sides are `≍ μ·a·K_ℓ⁻²` with constants `1/64 ≤ 3/100`.
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

/-! ## 1. Elementary quadratic-form facts -/

/-- `x^(-(2:ℝ)) = (x²)⁻¹` for every real `x`. -/
lemma rw_neg_two_eq_inv_sq (x : ℝ) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ :=
  Work.BoseFixR.rpow_neg_two_eq_inv_sq x

/-- `⟨f, c·1 f⟩ = c·‖f‖²`. -/
lemma qw_one_smul {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) (c : ℝ) :
    F.qw f (c • (1 : F.H →ₗ[ℝ] F.H)) = c * F.normSq f := by
  simp [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq]

/-- `⟨f, 1 f⟩ = ‖f‖²`. -/
lemma qw_one {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) :
    F.qw f (1 : F.H →ₗ[ℝ] F.H) = F.normSq f := by
  simp [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq]

/-- `⟨f, (Σ_i a_i†a_i) f⟩ = Σ_i ‖a_i f‖² ≥ 0`. -/
lemma qw_sum_nOp_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) :
    0 ≤ F.qw f (∑ k : Mode, F.nOp k) := by
  have h1 : F.qw f (∑ k : Mode, F.nOp k) = ∑ k : Mode, F.bp ((F.nOp k) f) f := by
    simp only [Work.BoseB7.FockData.qw, LinearMap.sum_apply, map_sum]
  rw [h1]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [Work.BoseB7.FockData.nOp, LinearMap.comp_apply]
  rw [F.aDag_adjoint k (F.a k f) f]
  exact F.bp_nonneg (F.a k f)

/-- `⟨f, T.N f⟩ ≥ 0`. -/
lemma qw_TN_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F) (f : F.H) :
    0 ≤ F.qw f T.N := T.N_nonneg f

/-- `⟨f, gapOpT E f⟩ ≥ ℓ⁻²⟨f, T.N f⟩`: the `n₊^H` half of the gap is nonnegative. -/
lemma qw_gapOpT_ge {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (heT : 0 ≤ E.eT) (f : F.H) :
    E.ell ^ (-(2 : ℝ)) * F.qw f T.N ≤ F.qw f (T.gapOpT E) := by
  have hNH : 0 ≤ F.qw f T.NH := T.NH_nonneg f
  have hc : 0 ≤ E.eT * (E.d * E.ell) ^ (-(2 : ℝ)) :=
    mul_nonneg heT (by rw [rw_neg_two_eq_inv_sq]; positivity)
  rw [Work.BoseB7A.TildeData.gapOpT, Work.BoseB7.FockData.qw_add,
    Work.BoseB7.FockData.qw_smul, Work.BoseB7.FockData.qw_smul]
  have hprod : 0 ≤ (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) * F.qw f T.NH := mul_nonneg hc hNH
  linarith

/-- `⟨f, dNumOpR E R f⟩ ≥ 0` as soon as `|ℬ_k| ≤ 𝒜_k` on the region (a row of the gate). -/
lemma qw_dNumOpR_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : Mode → Prop)
    [DecidablePred R] (hAB : ∀ k, |E.B k| ≤ E.A k) (f : F.H) :
    0 ≤ F.qw f (F.dNumOpR E R) := by
  have h1 : F.qw f (F.dNumOpR E R)
      = ∑ i ∈ (Work.BoseB7.excited Mode).filter R, E.D i * F.qw f (F.bNumOp E.alpha i) := by
    rw [Work.BoseB7.FockData.dNumOpR, Work.BoseB7.FockData.regionSum]
    exact Work.BoseB7A.qw_finset_sum F f _ E.D (fun i => F.bNumOp E.alpha i)
  rw [h1]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Work.BoseB7.bNumOp_nonneg F E.alpha i f)
  exact Work.BoseB7.FockData.Dcoef_nonneg (hAB i)

/-! ## 2. The `eq:SimplifyKz` decomposition of `KzOpFS` -/

/-- **FS `eq:SimplifyKz`** in the `control3Q` shape: `KzOpFS` is the `c`-number, the Bogoliubov
quadratic, the χ-mode number term, one `controlWordHi` and the remaining gap reserve
`(b/2 − b/50)·gapOpT`. -/
theorem KzOpFS_decomp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) :
    KzOpFS F T E gHat0 ρ
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H)
        + KzBogFS F E ρ
        + (((ρ - E.mu) * E.W1 0) • (∑ k : Mode, F.nOp k))
        + controlWordHi T (KzEnvAt E ρ)
        - F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ))
        + (E.b / 2 - E.b / 50) • T.gapOpT (KzEnvAt E ρ) := by
  have hcoef1 : (E.b / 2) * E.ell ^ (-(2 : ℝ)) = E.b / (2 * E.ell ^ 2) := by
    rw [rw_neg_two_eq_inv_sq]; field_simp
  have hcoef2 : (E.b / 2) * (E.eT * (E.d * E.ell) ^ (-(2 : ℝ)))
      = E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) := by
    rw [rw_neg_two_eq_inv_sq, mul_pow]; field_simp
  have hgap : (E.b / (2 * E.ell ^ 2)) • T.N
        + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH
      = (E.b / 2) • T.gapOpT (KzEnvAt E ρ) := by
    simp only [KzEnvAt, Work.BoseB7A.TildeData.gapOpT, smul_add, smul_smul]
    rw [hcoef1, hcoef2]
  have hsplit : (E.b / 2 - E.b / 50) • T.gapOpT (KzEnvAt E ρ)
        + (E.b / 50) • T.gapOpT (KzEnvAt E ρ)
      = (E.b / 2) • T.gapOpT (KzEnvAt E ρ) := by
    rw [← add_smul]
    congr 1
    ring
  simp only [KzOpFS, controlWordHi]
  rw [hgap, hsplit.symm]
  simp only [KzEnvAt]
  abel

/-- The `qw`-form of `KzOpFS_decomp`. -/
lemma qw_KzOpFS_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) (f : F.H) :
    F.qw f (KzOpFS F T E gHat0 ρ)
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) * F.normSq f
        + F.qw f (KzBogFS F E ρ)
        + ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k)
        + F.qw f (controlWordHi T (KzEnvAt E ρ))
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
  rw [KzOpFS_decomp F T E gHat0 ρ hℓ hd]
  simp only [Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_sub,
    Work.BoseB7.FockData.qw_smul, qw_one]

/-! ## 3. The number-term / gap absorption (design `F9`) -/

/-- **The universal-constant comparison** `Cn·|ρ−μ|·|Ŵ₁(0)| ≤ (b/2 − b/50)·ℓ⁻²`.
Everything on both sides is `μ·a·K_ℓ⁻²`: the left is at most
`16·(μK_ℓ⁻²/(2¹⁴π))·16πa = μaK_ℓ⁻²/64` and the right is
`(1/32 − 1/800)·μaK_ℓ⁻² = (3/100)μaK_ℓ⁻²`. -/
lemma num_term_pays {v : ℝ³ → ℝ} {μ ρ W0 Cn ℓ Kl : ℝ} (hav : 0 < a v) (hμ : 0 < μ)
    (hCn0 : 0 ≤ Cn) (hCn : Cn ≤ 16) (hW : |W0| ≤ 16 * Real.pi * a v)
    (hρ : |ρ - μ| ≤ μ * Kl ^ (-(2 : ℝ)) / (2 ^ 14 * Real.pi))
    (hℓ : ℓ ^ (-(2 : ℝ)) = Kl ^ (-(2 : ℝ)) * (μ * a v)) :
    Cn * |ρ - μ| * |W0| ≤ (1 / 2 - 1 / 50) * (1 / 16 : ℝ) * ℓ ^ (-(2 : ℝ)) := by
  have hKl0 : 0 ≤ Kl ^ (-(2 : ℝ)) := by
    rw [rw_neg_two_eq_inv_sq]; positivity
  have hμa : 0 < μ * a v := mul_pos hμ hav
  have h1 : Cn * |ρ - μ| * |W0| ≤ Cn * (μ * Kl ^ (-(2 : ℝ)) / (2 ^ 14 * Real.pi))
      * (16 * Real.pi * a v) := by
    have h2 : 0 ≤ Cn * (μ * Kl ^ (-(2 : ℝ)) / (2 ^ 14 * Real.pi)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hρ hCn0) hW (abs_nonneg _) h2
  have h3 : Cn * (μ * Kl ^ (-(2 : ℝ)) / (2 ^ 14 * Real.pi)) * (16 * Real.pi * a v)
      = Cn * 16 * (μ * a v) * Kl ^ (-(2 : ℝ)) / 2 ^ 14 := by
    field_simp
  have h4 : Cn * 16 * (μ * a v) * Kl ^ (-(2 : ℝ)) / 2 ^ 14
      ≤ 16 * 16 * (μ * a v) * Kl ^ (-(2 : ℝ)) / 2 ^ 14 := by
    have h5 : 0 ≤ 16 * (μ * a v) * Kl ^ (-(2 : ℝ)) / 2 ^ 14 := by positivity
    linarith [mul_le_mul_of_nonneg_right hCn h5]
  have h6 : 16 * 16 * (μ * a v) * Kl ^ (-(2 : ℝ)) / 2 ^ 14
      = (μ * a v) * Kl ^ (-(2 : ℝ)) * (1 / 64) := by
    norm_num; ring
  have h7 : (μ * a v) * Kl ^ (-(2 : ℝ)) * (1 / 64)
      ≤ (μ * a v) * Kl ^ (-(2 : ℝ)) * (3 / 100) := by
    have h8 : (1 / 64 : ℝ) ≤ 3 / 100 := by norm_num
    exact mul_le_mul_of_nonneg_left h8 (mul_nonneg hμa.le hKl0)
  have h9 : (μ * a v) * Kl ^ (-(2 : ℝ)) * (3 / 100)
      = (1 / 2 - 1 / 50) * (1 / 16 : ℝ) * (Kl ^ (-(2 : ℝ)) * (μ * a v)) := by
    norm_num; ring
  rw [hℓ]
  linarith [h1, h3, h4, h6, h7, h9]

/-- The two projections of a `min`-bound. -/
lemma le_of_le_min {a b c : ℝ} (h : a ≤ min b c) : a ≤ b ∧ a ≤ c :=
  ⟨le_trans h (min_le_left (a := b) (b := c)), le_trans h (min_le_right (a := b) (b := c))⟩

/-! ## 4. The close case at one parameter point (FS §11) -/

/-- **FS §11's close-case estimate at one parameter point.**  Everything the argument
consumes is an explicit hypothesis: the view `RViewFS`, the combined Bogoliubov input
`hbog_at` (FS `eq:Combined1` at the level of `KzOpFS`), the Control3Q input `hctrl_at`
(FS `thm:Control3Q`), the gate `hKK` and the gap tie `hb0E`.  This is the form in which
`RB67FS_of_pieces` applies it at the honest family. -/
theorem RB67FS_close_step {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hR : 0 < R) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (g0 : ℝ)
    {μ ε₀ t₀ Cb Cc : ℝ} {K₀ b₀ : ℝ} (hCc : 0 ≤ Cc)
    (hAdm : Adm v ε₀ μ) (hε₀_le_t : ε₀ ≤ t₀) (hε₀_le_1 : ε₀ ≤ 1)
    (hεR : ε₀ ≤ (a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
    (hεh : ε₀ ≤ (1 / 2 : ℝ) ^ (323 / 3 : ℝ))
    (hview : RViewFS v h μ F T E g0)
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
      (hv' : Work.BoseB7.FSParamsView E'), hv'.t ≤ t₀ → b₀ ≤ E'.b → Q3KernelFS K₀ F' T' E' →
        ∀ Φ : F'.H, T'.NWindow E'.bigM Φ →
          -(Cc * Work.BoseB7A.controlErrA E') * F'.normSq Φ ≤ F'.qw Φ (controlWordHi T' E'))
    (hb0E : b₀ ≤ E.b)
    (hKK : ∀ (ρ : ℝ), CloseCondFS v μ ρ → Q3KernelFS K₀ F T (KzEnvAt E ρ)) :
    ∀ (ρ : ℝ), 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f : F.H, T.NWindow E.bigM f →
      CloseBoundR v R μ (Cb + Cc) ρ * F.normSq f ≤ F.qw f (KzOpFS F T E g0 ρ) := by
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
  have hgateK : Q3KernelFS K₀ F T (KzEnvAt E ρ) := hKK ρ hclose
  have hbE : b₀ ≤ (KzEnvAt E ρ).b := hb0E
  have ht_le : hE'FSP.t ≤ t₀ := by
    rw [hE'FSP.mu_eq.symm]
    have e1 : (KzEnvAt E ρ).mu = μ := hmu
    have e2 : (KzEnvAt E ρ).aScat = a v := haSc
    rw [e1, e2]
    exact le_trans hAdm.2.1 hε₀_le_t
  have hctrlE : -(Cc * Work.BoseB7A.controlErrA (KzEnvAt E ρ)) * F.normSq f
      ≤ F.qw f (controlWordHi T (KzEnvAt E ρ)) :=
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
  -- ## 6. the decomposition of `KzOpFS`
  have hdec' : F.qw f (KzOpFS F T E g0 ρ)
      = c₀b * n2 + F.qw f (KzBogFS F E ρ)
        + ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k)
        + F.qw f (controlWordHi T (KzEnvAt E ρ))
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
    rw [qw_KzOpFS_eq F T E g0 ρ hellne hdne f, hc₀b, hn2]
  have hstep1 : (Wb - Cb * KQ - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3) * n2
      ≤ F.qw f (KzBogFS F E ρ)
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ))) := by
    linarith [hbogE]
  have hmain : (c₀b - Mb - 4 * π * (ρ - E.mu) ^ 2 * (a v) * E.ell ^ 3 + Wb - Cb * KQ - Cc * cE)
        * n2 ≤ F.qw f (KzOpFS F T E g0 ρ) := by
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
    _ ≤ F.qw f (KzOpFS F T E g0 ρ) := hmain

/-! ## 5. The close-case residual at the honest family -/

theorem RB67FS_of_pieces {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) {K₀ b₀ : ℝ} (hb₀ : 0 < b₀) {εg : ℝ} (hεg : 0 < εg)
    (hgate : HonestGateAtFS v h fc fu HM εg K₀ b₀) (hctrl : Control3QFS K₀ b₀ hb₀)
    (hbog : BogOpBoundFS v h R (HonestBoxFam v h fc fu HM)) :
    RB67FS v h R (HonestBoxFam v h fc fu HM) := by
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
  have hstep := RB67FS_close_step (v := v) (h := h) (R := R)
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
