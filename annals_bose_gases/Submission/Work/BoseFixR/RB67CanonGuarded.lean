import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.CanonViewFalse
import Submission.Work.BoseFixR.FSParamsViewCanon
import Submission.Work.BoseFixR.FSParamsView_KzEnvAt
import Submission.Work.BoseFixR.KzOpDecompV2
import Submission.Work.BoseFixR.Pieces
import Submission.Work.BoseFixR.adm_R_le_ell_chiR0
import Submission.Work.BoseFixR.bracket_quadratic
import Submission.Work.BoseFixR.dil_rpow_half
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/RB67CanonGuarded.lean`

FS §10 + §11's close-region bound `RB67` at the canonical family, **guarded
gate version**: the §10 input is `Control3QGuarded'` (the gate is BoseK15's
honest bundle `Work.BoseK15.Q3Kernel'`) and the gate instance is supplied as the
hypothesis `hKK` on the close range, together with the gap lower bound
`b₀ ≤ E.b` (`hb₀b`) and FS's combined `eq:Combined1` Bogoliubov bound `hbog`.

The proof is the same §11 arithmetic as
`RB67CanonOfPiecesV2.RB67_of_view_KzKernels` (where the gate is the local
`KzKernels` copy).  Since the gate is passed to `hctrl'` and never inspected, the
argument only has to be replayed with `Control3QGuarded'`/`Q3Kernel'` in place of
`Control3QGuarded`/`KzKernels`; the auxiliary `qw`-estimates of that module are
reproduced below, so that this file is self-contained: every module it imports is
unconditionally proved.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! ## 1. `chat W 0 = pairW W 0` and the uniform bound `|Ŵ₁(0)| ≤ 16π a v` -/

/-- The two Fourier conventions agree at the origin: `chat W 0 = pairW W 0`. -/
lemma chat_zero_eq_pairW (W : EuclideanSpace ℝ (Fin 3) → ℝ) : chat W 0 = pairW W 0 := by
  have h1 : chat W 0 = (FourierTransform.fourier
      (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))
      ((2 * Real.pi)⁻¹ • (0 : EuclideanSpace ℝ (Fin 3)))).re := by
    rw [chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [h1, pairW_eq_cfourier_re]
  simp [Submission.BoseGases.cfourier]

/-- **`|Ŵ₁(0)| ≤ 16π·(a v)`** for `W₁ = wScaled ℓ (g0 v h)`: the `q = 0` case of
the corpus's `abs_pairW_wScaled_g0_le` (FS `eq:WSestimate`, `C₀ = 16π`). -/
theorem abs_chat_W1fun_zero_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    |chat (W1fun v h ℓ) 0| ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  rw [chat_zero_eq_pairW]
  exact Submission.BoseGases.abs_pairW_wScaled_g0_le hR hv hvrad hv_supp h hℓ hRℓ 0

/-! ## 2. The `qw`-estimates for the slots of `KzOp` -/

/-- `⟨f, (c • 1)f⟩ = c·‖f‖²`. -/
lemma qw_one_smul {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) (c : ℝ) :
    F.qw f (c • (1 : F.H →ₗ[ℝ] F.H)) = c * F.normSq f := by
  simp [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq]

/-- `⟨f, 1·f⟩ = ‖f‖²`. -/
lemma qw_one {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) :
    F.qw f (1 : F.H →ₗ[ℝ] F.H) = F.normSq f := by
  simp [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq]

/-- `⟨f, n₊f⟩ ≥ 0`. -/
lemma qw_nPlus_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (f : F.H) : 0 ≤ F.qw f F.nPlus :=
  Work.BoseB7.BNumOpAux.bp_nPlus_nonneg F f

/-- `⟨f, (dNumOpR E True)f⟩ ≥ 0` as soon as `|ℬ_k| ≤ 𝒜_k` (a field of
`KzKernels`, so it holds on the close range). -/
lemma qw_dNumOpR_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (hAB : ∀ k : Mode, |E.B k| ≤ E.A k) (f : F.H) :
    0 ≤ F.qw f (F.dNumOpR E (fun _ => True)) := by
  have h1 : F.qw f (F.dNumOpR E (fun _ => True))
      = ∑ i ∈ (Work.BoseB7.excited Mode).filter (fun _ => True),
          E.D i * F.qw f (F.bNumOp E.alpha i) := by
    rw [Work.BoseB7.FockData.dNumOpR, Work.BoseB7.FockData.regionSum]
    exact Work.BoseB7A.qw_finset_sum F f _ E.D (fun i => F.bNumOp E.alpha i)
  rw [h1]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (Work.BoseB7.FockData.Dcoef_nonneg (hAB i))
    (Work.BoseB7.bNumOp_nonneg F E.alpha i f)

/-- `⟨f, gapOpT E f⟩ ≥ 0` (both coefficients are nonnegative and `n₊`, `n₊^H`
are positive operators). -/
lemma qw_gapOpT_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (heT : 0 ≤ E.eT) (hd : E.d ≠ 0) (hℓ : E.ell ≠ 0) (f : F.H) :
    0 ≤ F.qw f (T.gapOpT E) := by
  rw [Work.BoseB7A.TildeData.gapOpT, Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_smul,
    Work.BoseB7.FockData.qw_smul]
  have h1 : 0 ≤ E.ell ^ (-(2 : ℝ)) * F.qw f T.N := by
    rw [rpow_neg_two_eq_inv_sq]
    refine mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) ?_
    rw [Work.BoseB7.FockData.qw]; exact T.N_nonneg f
  have h2 : 0 ≤ (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) * F.qw f T.NH := by
    rw [rpow_neg_two_eq_inv_sq]
    refine mul_nonneg (mul_nonneg heT ?_) ?_
    · exact inv_nonneg.mpr (sq_nonneg _)
    · rw [Work.BoseB7.FockData.qw]; exact T.NH_nonneg f
  linarith

/-- On a window state, `⟨f, n₊f⟩ ≤ 𝓜‖f‖²` — the view's `n₊ ≤ N` plus FS's window
`eq:LocalizedAftercNumber`. -/
lemma qw_nPlus_le_bigM {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F) {E : Work.BoseB7.Q3Env Mode}
    (hnPlusN : ∀ f : F.H, F.qw f F.nPlus ≤ F.qw f T.N)
    (hM : 0 ≤ E.bigM) {f : F.H} (hf : T.NWindow E.bigM f) :
    F.qw f F.nPlus ≤ E.bigM * F.normSq f :=
  le_trans (hnPlusN f) (Work.BoseB7A.NWindow_bp_N_le F T hM hf)

/-- The `qw`-form of `KzOpDecompV2`: the quadratic form of `KzOp` is the sum of
the quadratic forms of its five groups. -/
lemma qw_KzOp_eq {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) (f : F.H) :
    F.qw f (KzOp F T E gHat0 ρ)
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) * F.normSq f
        + (F.qw f (KzBog F E ρ) - F.qw f (F.dNumOpR (KzEnvAt E ρ) (fun _ => True)))
        + ((ρ - E.mu) * E.W1 0) * F.qw f F.nPlus
        + F.qw f (T.controlWordT (KzEnvAt E ρ))
        + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
  have hdec := KzOpDecompV2 F T E gHat0 ρ hℓ hd
  rw [hdec]
  simp only [Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_sub,
    Work.BoseB7.FockData.qw_smul, qw_one]

/-- The two projections of a `min`-bound. -/
lemma le_of_le_min {a b c : ℝ} (h : a ≤ min b c) : a ≤ b ∧ a ≤ c :=
  ⟨le_trans h (min_le_left (a := b) (b := c)), le_trans h (min_le_right (a := b) (b := c))⟩

/-! ## 3. The corrected close bound

`RB67` at the canonical family from the view *plus* the `KzKernels K₀` datum that
`Control3QGuarded K₀` consumes (at the same `K₀`), and the gap lower bound
`b₀ ≤ E.b`. -/

theorem RB67_of_view_Q3Kernel' {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v)
    {K₀ b₀ : ℝ} (hb₀ : 0 < b₀)
    (hctrl : Work.BoseFixR.Control3QGuarded' K₀ b₀ hb₀)
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
    (fc : Work.BoseBoxFix.LowCut)
    (hbog : Work.BoseFixR.BogOpBound v h R (Work.BoseFixR.KzCanonFam v h Mode F T fc))
    (hKK : ∀ μ : ℝ, (Work.BoseFixR.KzCanonFam v h Mode F T fc μ).view v h μ →
      ∀ ρ : ℝ, Work.BoseFixR.CloseCond v μ ρ →
        Work.BoseK15.Q3Kernel' K₀ F T
          (Work.BoseFixR.KzEnvAt (Work.BoseFixR.KzEnvFs v h μ F fc) ρ))
    (hb₀b : ∀ μ : ℝ, (Work.BoseFixR.KzCanonFam v h Mode F T fc μ).view v h μ →
      b₀ ≤ (Work.BoseFixR.KzEnvFs v h μ F fc).b) :
    Work.BoseFixR.RB67 v h R (Work.BoseFixR.KzCanonFam v h Mode F T fc) := by
  obtain ⟨ε₀b, Cb, hε₀b, hCb, hbog'⟩ := hbog
  obtain ⟨Cc, t₀, hCc, ht₀, hctrl'⟩ := hctrl
  have hchiR0 : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  set εR : ℝ := (BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) with hεR
  set εh : ℝ := (1 / 2 : ℝ) ^ (323 / 3 : ℝ) with hεh
  set ε₀ : ℝ := min ε₀b (min t₀ (min 1 (min εR εh))) with hε₀
  have hεRpos : 0 < εR := by
    rw [hεR]; exact Real.rpow_pos_of_pos (by positivity) _
  have hεhpos : 0 < εh := by
    rw [hεh]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]; exact lt_min hε₀b (lt_min ht₀ (lt_min one_pos (lt_min hεRpos hεhpos)))
  obtain ⟨hε₀_le_b, hε₁⟩ : ε₀ ≤ ε₀b ∧ ε₀ ≤ min t₀ (min 1 (min εR εh)) :=
    le_of_le_min (a := ε₀) (by rw [hε₀])
  obtain ⟨hε₀_le_t, hε₂⟩ := le_of_le_min (a := ε₀) hε₁
  obtain ⟨hε₀_le_1, hε₃⟩ := le_of_le_min (a := ε₀) hε₂
  obtain ⟨hε₀_le_R, hε₀_le_h⟩ := le_of_le_min (a := ε₀) hε₃
  refine ⟨ε₀, Cb + Cc + 16 * π, hε₀pos, ?_, ?_⟩
  · positivity
  intro μ hAdm hview ρ hρ hclose f hwin
  -- ## 0. the smallness data
  have hμ : 0 < μ := hAdm.1
  have hAdm_b : Adm v ε₀b μ := adm_mono hε₀_le_b hAdm
  have hdilpos : 0 < dil v μ := by rw [dil]; positivity
  have hdil1 : dil v μ ≤ 1 := le_trans hAdm.2.1 hε₀_le_1
  have hRell : R ≤ ell v μ * Submission.BoseGases.chiR0 :=
    adm_R_le_ell_chiR0 hR hav (by rw [← hεR]; exact hε₀_le_R) hAdm
  have hhalf : (dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2 :=
    dil_rpow_half hAdm (by rw [← hεh]; exact hε₀_le_h)
  have hellpos : 0 < ell v μ := ell_pos' v hμ hav
  -- ## 1. the view
  have hviewE : RView v h μ F T (KzEnvFs v h μ F fc) (8 * π * a v) := hview
  have hviewE' := hviewE
  obtain ⟨hFSPne, hmu, haSc, hell, hbigM, hb, hd, hs, heT, hintM, hg0, htau, hA, hB,
    hW1, hW1o, hW1o0, hchi, hchiSq, hfL, hnPlusN, hviewKK⟩ := hviewE'
  have hFSP : Work.BoseB7.FSParamsView (KzEnvFs v h μ F fc) := hFSPne.some
  -- ## 2. the target, in explicit form
  change CloseBoundR v R μ (Cb + Cc + 16 * π) ρ * F.normSq f
      ≤ F.qw f (KzOp F T (KzEnvFs v h μ F fc) (8 * π * a v) ρ)
  -- ## 3. abbreviations
  set n2 : ℝ := F.normSq f with hn2
  set c₀b : ℝ := (KzEnvFs v h μ F fc).ell ^ 3 *
      (-(1 / 2) * (KzEnvFs v h μ F fc).mu ^ 2 * (8 * π * a v)
        + (1 / 2) * (ρ - (KzEnvFs v h μ F fc).mu) ^ 2 * (8 * π * a v)
        + (1 / 2) * ρ ^ 2 * (KzEnvFs v h μ F fc).W1omega0) with hc₀b
  set Mb : ℝ := (1 / 2) * ρ ^ 2 * (KzEnvFs v h μ F fc).ell ^ 3
      * (KzEnvFs v h μ F fc).W1omega0 with hMb
  set Wb : ℝ := 4 * π * lhyC * ρ ^ 2 * BoseGases.a v * ell3 v μ
      * Real.sqrt (ρ * BoseGases.a v ^ 3) with hWb
  set KQ : ℝ := μ ^ 2 * BoseGases.a v * ell3 v μ * Real.sqrt (dil v μ)
      * (fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) with hKQ
  set cE : ℝ := Work.BoseB7A.controlErrA (KzEnvAt (KzEnvFs v h μ F fc) ρ) with hcE
  -- ## 4. the close-range data
  have hρpos : 0 < ρ := by
    have hthr : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [closeThreshold, Kl_inv_sq v hμ hav]
    have h2 : |ρ - μ| ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := by rw [← hthr]; exact hclose
    have h3 : -(ρ - μ) ≤ |ρ - μ| := neg_le_abs _
    nlinarith [h2, h3, hμ, hhalf]
  have hE'_FSP : Work.BoseB7.FSParamsView (KzEnvAt (KzEnvFs v h μ F fc) ρ) :=
    (FSParamsView_KzEnvAt (E := KzEnvFs v h μ F fc) hFSP hρpos
      (by rw [hell]; exact ne_of_gt hellpos)
      (by
        rw [hmu]
        have hthr : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
          rw [closeThreshold, Kl_inv_sq v hμ hav]
        have h2 : |ρ - μ| ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := by rw [← hthr]; exact hclose
        nlinarith [h2, hhalf, hμ])).some
  have hKKρ : Work.BoseK15.Q3Kernel' K₀ F T (KzEnvAt (KzEnvFs v h μ F fc) ρ) :=
    hKK μ hview ρ hclose
  have hbE : b₀ ≤ (KzEnvAt (KzEnvFs v h μ F fc) ρ).b := by
    have h1 := hb₀b μ hview
    simpa only [KzEnvAt] using h1
  -- the window, in the explicit form
  have hwinE : T.NWindow (KzEnvFs v h μ F fc).bigM f := hwin
  have hwinE' : T.NWindow (KzEnvAt (KzEnvFs v h μ F fc) ρ).bigM f := hwinE
  -- ## 5. `hctrl` and `hbog` at `(μ, ρ, f)`
  have ht_le : hE'_FSP.t ≤ t₀ := by
    rw [hE'_FSP.mu_eq.symm]
    show μ * BoseGases.a v ^ 3 ≤ t₀
    exact le_trans hAdm.2.1 hε₀_le_t
  have hctrlE : -(Cc * cE) * n2 ≤ F.qw f (T.controlWordT (KzEnvAt (KzEnvFs v h μ F fc) ρ)) := by
    have h1 : -(Cc * Work.BoseB7A.controlErrA (KzEnvAt (KzEnvFs v h μ F fc) ρ)) * F.normSq f
        ≤ F.qw f (T.controlWordT (KzEnvAt (KzEnvFs v h μ F fc) ρ)) :=
      hctrl' F T (KzEnvAt (KzEnvFs v h μ F fc) ρ) hE'_FSP ht_le hbE hKKρ f hwinE'
    rw [hcE, hn2]
    exact h1
  have hbogE : (Wb - Cb * KQ) * n2
      + F.qw f (F.dNumOpR (KzEnvAt (KzEnvFs v h μ F fc) ρ) (fun _ => True))
      ≤ F.qw f (KzBog F (KzEnvFs v h μ F fc) ρ) + Mb * n2 := by
    have h1 : (4 * π * lhyC * ρ ^ 2 * BoseGases.a v * ell3 v μ * Real.sqrt (ρ * BoseGases.a v ^ 3)
        - Cb * μ ^ 2 * BoseGases.a v * ell3 v μ * Real.sqrt (dil v μ)
            * (fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
        * F.normSq f
        + F.qw f (F.dNumOpR (KzEnvAt (KzEnvFs v h μ F fc) ρ) (fun _ => True))
        ≤ F.qw f (KzBog F (KzEnvFs v h μ F fc) ρ)
          + ((1 / 2) * ρ ^ 2 * (KzEnvFs v h μ F fc).ell ^ 3 * (KzEnvFs v h μ F fc).W1omega0)
              * F.normSq f :=
      hbog' μ hAdm_b hviewE ρ hρ hclose f hwinE
    have eK : Cb * μ ^ 2 * BoseGases.a v * ell3 v μ * Real.sqrt (dil v μ)
        * (fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ)
        = Cb * KQ := by rw [hKQ]; ring
    simp only [eK, ← hWb, ← hMb, ← hn2] at h1
    exact h1
  -- ## 6. the decomposition of `KzOp`
  have hℓne : (KzEnvFs v h μ F fc).ell ≠ 0 := by rw [hell]; exact ne_of_gt hellpos
  have hdne : (KzEnvFs v h μ F fc).d ≠ 0 := by
    rw [hd]; exact ne_of_gt (fsXp_pos hdilpos)
  have hdecomp : F.qw f (KzOp F T (KzEnvFs v h μ F fc) (8 * π * a v) ρ)
      = c₀b * n2
        + (F.qw f (KzBog F (KzEnvFs v h μ F fc) ρ)
            - F.qw f (F.dNumOpR (KzEnvAt (KzEnvFs v h μ F fc) ρ) (fun _ => True)))
        + ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0)
            * (F.qw f F.nPlus)
        + F.qw f (T.controlWordT (KzEnvAt (KzEnvFs v h μ F fc) ρ))
        + ((KzEnvFs v h μ F fc).b / 2 - (KzEnvFs v h μ F fc).b / 50)
            * F.qw f (T.gapOpT (KzEnvAt (KzEnvFs v h μ F fc) ρ)) := by
    rw [qw_KzOp_eq F T (KzEnvFs v h μ F fc) (8 * π * a v) ρ hℓne hdne f, ← hc₀b, ← hn2]
  -- ## 7. the slot estimates
  have hn2nn : 0 ≤ n2 := by rw [hn2]; exact F.normSq_nonneg f
  have hbigMnn : 0 ≤ (KzEnvFs v h μ F fc).bigM := by
    rw [KzEnvFs_bigM_val (F := F) (fc := fc) (μ := μ) (h := h) (v := v) hdilpos]
    exact fsXp_nonneg (c := (-(327 / 4) : ℝ)) (le_of_lt hdilpos)
  have hnPlus_nn : 0 ≤ F.qw f F.nPlus := qw_nPlus_nonneg F f
  have hnPlus_le : F.qw f F.nPlus ≤ (KzEnvFs v h μ F fc).bigM * n2 := by
    have h1 := qw_nPlus_le_bigM T hnPlusN hbigMnn hwinE
    rwa [← hn2] at h1
  have heTpos : 0 ≤ (KzEnvAt (KzEnvFs v h μ F fc) ρ).eT := by
    rw [show (KzEnvAt (KzEnvFs v h μ F fc) ρ).eT = (KzEnvFs v h μ F fc).eT from rfl, heT]
    show 0 ≤ Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (23 / 4)
    exact (fsXp_pos hdilpos).le
  have hgap_nn : 0 ≤ F.qw f (T.gapOpT (KzEnvAt (KzEnvFs v h μ F fc) ρ)) :=
    qw_gapOpT_nonneg T _ heTpos
      (by rw [show (KzEnvAt (KzEnvFs v h μ F fc) ρ).d = (KzEnvFs v h μ F fc).d from rfl]; exact hdne)
      (by rw [show (KzEnvAt (KzEnvFs v h μ F fc) ρ).ell = (KzEnvFs v h μ F fc).ell from rfl];
          exact hℓne) f
  have hbvalue : (KzEnvFs v h μ F fc).b = 1 / 16 := by
    rw [hb]; rfl
  have hbpos : 0 ≤ (KzEnvFs v h μ F fc).b / 2 - (KzEnvFs v h μ F fc).b / 50 := by
    rw [hbvalue]; norm_num
  have hW0 : |(KzEnvFs v h μ F fc).W1 0| ≤ 16 * Real.pi * BoseGases.a v := by
    rw [hW1]
    show |chat (W1fun v h (ell v μ)) (F.kmom 0)| ≤ 16 * Real.pi * BoseGases.a v
    rw [kmom_zero]
    exact abs_chat_W1fun_zero_le hR hv hvrad hv_supp hellpos hRell
  have hquad : 16 * Real.pi * KQ
      + 4 * Real.pi * |ρ - μ| ^ 2 * BoseGases.a v * ell3 v μ
      ≥ |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM := by
    have hbm : (KzEnvFs v h μ F fc).bigM = fsXp (dil v μ) (-(327 / 4)) :=
      KzEnvFs_bigM_val (F := F) (fc := fc) (μ := μ) (h := h) (v := v) hdilpos
    have h := bracket_quadratic (v := v) (μ := μ) (R := R) (W0 := (KzEnvFs v h μ F fc).W1 0)
      (bM := (KzEnvFs v h μ F fc).bigM) (x := |ρ - μ|) hμ hav (le_of_lt hR) hdil1 hW0 hbm
      (abs_nonneg _)
    rw [hKQ]
    exact h
  have hcE_le : cE ≤ KQ := by
    have hell3 : ell3 v μ = ell v μ ^ 3 := rfl
    have hEμ : (KzEnvAt (KzEnvFs v h μ F fc) ρ).mu = μ := hmu
    have hEa : (KzEnvAt (KzEnvFs v h μ F fc) ρ).aScat = BoseGases.a v := haSc
    have hEl : (KzEnvAt (KzEnvFs v h μ F fc) ρ).ell = ell v μ := hell
    have hdilE : Work.BoseB7.dil (KzEnvAt (KzEnvFs v h μ F fc) ρ) (1 / 2 + 1 / 323)
        = (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ) := by
      rw [Work.BoseB7.dil, hEμ, hEa]
      rfl
    have hcore : (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ)
        ≤ Real.sqrt (dil v μ) * (fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2
            * Real.sqrt (dil v μ) + errExp v μ) := by
      have h1 : (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ)
          = Real.sqrt (dil v μ) * (dil v μ) ^ (1 / 323 : ℝ) := by
        rw [Real.rpow_add hdilpos, Real.sqrt_eq_rpow]
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      have h2 : (dil v μ) ^ (1 / 323 : ℝ) ≤ errExp v μ := by
        rw [errExp]
        exact Real.rpow_le_rpow_of_exponent_ge hdilpos hdil1 (by norm_num)
      linarith [h2, sq_nonneg (fsX v μ),
        mul_nonneg (sq_nonneg (R / BoseGases.a v)) (Real.sqrt_nonneg (dil v μ))]
    have hcEeq : cE = (dil v μ) ^ (1 / 2 + 1 / 323 : ℝ)
        * (μ ^ 2 * BoseGases.a v * ell3 v μ) := by
      rw [hcE, Work.BoseB7A.controlErrA, Work.BoseB7A.E0, hdilE, hEμ, hEa, hEl, ← hell3]
      ring
    have hKQeq : KQ = (Real.sqrt (dil v μ) * (fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2
        * Real.sqrt (dil v μ) + errExp v μ)) * (μ ^ 2 * BoseGases.a v * ell3 v μ) := by
      rw [hKQ]; ring
    rw [hcEeq, hKQeq]
    exact mul_le_mul_of_nonneg_right hcore (by rw [ell3]; positivity)
  -- ## 8. assemble
  have hstep1 : (Wb - Cb * KQ - Mb) * n2
      ≤ F.qw f (KzBog F (KzEnvFs v h μ F fc) ρ)
        - F.qw f (F.dNumOpR (KzEnvAt (KzEnvFs v h μ F fc) ρ) (fun _ => True)) := by
    linarith [hbogE]
  have hstep3 : -(|ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM) * n2
      ≤ ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0) * (F.qw f F.nPlus) := by
    have hcoef : -(|ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM) * n2
        ≤ -(|ρ - μ| * |(KzEnvFs v h μ F fc).W1 0|) * ((KzEnvFs v h μ F fc).bigM * n2) := by
      nlinarith [hbigMnn, hn2nn, abs_nonneg (ρ - μ), abs_nonneg ((KzEnvFs v h μ F fc).W1 0)]
    have hcoef2 : -(|ρ - μ| * |(KzEnvFs v h μ F fc).W1 0|)
        ≤ (ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0 := by
      have h1 : |(ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0|
          = |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| := by rw [abs_mul, hmu]
      linarith [neg_abs_le ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0), h1]
    by_cases hs : 0 ≤ (ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0
    · have h2 : 0 ≤ ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0)
          * (F.qw f F.nPlus) := mul_nonneg hs hnPlus_nn
      have hY : 0 ≤ |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM * n2 := by
        positivity
      linarith [h2, hY]
    · push_neg at hs
      have h3 : ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0) * (F.qw f F.nPlus)
          ≥ ((ρ - (KzEnvFs v h μ F fc).mu) * (KzEnvFs v h μ F fc).W1 0)
              * ((KzEnvFs v h μ F fc).bigM * n2) :=
        mul_le_mul_of_nonpos_left hnPlus_le hs.le
      nlinarith [hcoef, hcoef2, h3]
  have hstep4 : 0 ≤ ((KzEnvFs v h μ F fc).b / 2 - (KzEnvFs v h μ F fc).b / 50)
      * F.qw f (T.gapOpT (KzEnvAt (KzEnvFs v h μ F fc) ρ)) :=
    mul_nonneg hbpos hgap_nn
  have hmain : F.qw f (KzOp F T (KzEnvFs v h μ F fc) (8 * π * a v) ρ)
      ≥ (c₀b - Mb + Wb - Cb * KQ - Cc * cE
          - |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM) * n2 := by
    rw [hdecomp]
    linarith [hstep1, hctrlE, hstep3, hstep4]
  -- ## 9. the arithmetic comparison
  have hc0 : c₀b - Mb
      = -(4 * Real.pi * μ ^ 2 * BoseGases.a v * ell3 v μ)
        + 4 * Real.pi * (ρ - μ) ^ 2 * BoseGases.a v * ell3 v μ := by
    rw [hc₀b, hMb, hmu]
    have hell3 : (KzEnvFs v h μ F fc).ell ^ 3 = ell3 v μ := by rw [hell]; rfl
    rw [hell3]
    ring
  have hgoal : CloseBoundR v R μ (Cb + Cc + 16 * Real.pi) ρ
      ≤ c₀b - Mb + Wb - Cb * KQ - Cc * cE
          - |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM := by
    have h1 : Cc * cE ≤ Cc * KQ := mul_le_mul_of_nonneg_left hcE_le hCc
    have h3 : CloseBoundR v R μ (Cb + Cc + 16 * Real.pi) ρ
        = -(4 * Real.pi * μ ^ 2 * BoseGases.a v * ell3 v μ)
          + Wb - (Cb + Cc + 16 * Real.pi) * KQ := by
      rw [CloseBoundR, hWb, hKQ]
      ring
    rw [h3, hc0]
    have e1 : 0 ≤ Cc * KQ - Cc * cE := by linarith [h1]
    have e2 : 0 ≤ 16 * Real.pi * KQ + 4 * Real.pi * (ρ - μ) ^ 2 * BoseGases.a v * ell3 v μ
        - |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM := by
      have h := hquad
      have hsq : |ρ - μ| ^ 2 = (ρ - μ) ^ 2 := sq_abs (ρ - μ)
      rw [hsq] at h
      linarith [h]
    have h4 : 0 ≤ 4 * Real.pi * (ρ - μ) ^ 2 * BoseGases.a v * ell3 v μ := by
      have hℓ3 : 0 ≤ ell3 v μ := by
        rw [ell3]; exact pow_nonneg (le_of_lt (ell_pos' v hμ hav)) 3
      positivity
    have e4 : (Cb + Cc + 16 * Real.pi) * KQ = Cb * KQ + Cc * KQ + 16 * Real.pi * KQ := by ring
    linarith [e1, e2, e4, h4]
  calc CloseBoundR v R μ (Cb + Cc + 16 * π) ρ * F.normSq f
      = CloseBoundR v R μ (Cb + Cc + 16 * π) ρ * n2 := by rw [hn2]
    _ ≤ (c₀b - Mb + Wb - Cb * KQ - Cc * cE
          - |ρ - μ| * |(KzEnvFs v h μ F fc).W1 0| * (KzEnvFs v h μ F fc).bigM) * n2 :=
        mul_le_mul_of_nonneg_right hgoal hn2nn
    _ ≤ F.qw f (KzOp F T (KzEnvFs v h μ F fc) (8 * π * a v) ρ) := hmain

/-- **The requested lemma**: `RB67` at the canonical family from the guarded §10
input `Control3QGuarded'` (gated on BoseK15's honest `Q3Kernel'`, supplied on the
close range by `hKK`) plus the gap bound `hb₀b` and FS's combined
`eq:Combined1` Bogoliubov bound `hbog`. -/

theorem RB67CanonGuarded {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v)
    {K₀ b₀ : ℝ} (hb₀ : 0 < b₀)
    (hctrl : Work.BoseFixR.Control3QGuarded' K₀ b₀ hb₀)
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
    (fc : Work.BoseBoxFix.LowCut)
    (hbog : Work.BoseFixR.BogOpBound v h R (Work.BoseFixR.KzCanonFam v h Mode F T fc))
    (hKK : ∀ μ : ℝ, (Work.BoseFixR.KzCanonFam v h Mode F T fc μ).view v h μ →
      ∀ ρ : ℝ, Work.BoseFixR.CloseCond v μ ρ →
        Work.BoseK15.Q3Kernel' K₀ F T
          (Work.BoseFixR.KzEnvAt (Work.BoseFixR.KzEnvFs v h μ F fc) ρ))
    (hb₀b : ∀ μ : ℝ, (Work.BoseFixR.KzCanonFam v h Mode F T fc μ).view v h μ →
      b₀ ≤ (Work.BoseFixR.KzEnvFs v h μ F fc).b) :
    Work.BoseFixR.RB67 v h R (Work.BoseFixR.KzCanonFam v h Mode F T fc) :=
  RB67_of_view_Q3Kernel' h hv hvrad hR hv_supp hav hb₀ hctrl Mode F T fc hbog hKK hb₀b

end Work.BoseFixR
