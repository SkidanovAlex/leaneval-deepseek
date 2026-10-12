import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.All.FarCorr
import Submission.Work.BoseFixR.All.FarResidOp
import Submission.Work.BoseFixR.All.FarThreeQFixB
import Submission.Work.BoseFixR.All.extraLeA
import Submission.Work.BoseFixR.All.extraLeB
import Submission.Work.BoseFixR.All.farTauRowMid
import Submission.Work.BoseFixR.All.farZPGen
import Submission.Work.BoseFixR.All.farZPWin
import Submission.Work.BoseFixR.All.massDeficitFar
import Submission.Work.BoseFixR.All.zetaLeOne
import Submission.Work.BoseFixR.adm_100R_le_ell
import Submission.Work.BoseFixR.farArithExtra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/AsmFar.lean`

The far leg of FS §9 (`prop:FarAway`) at the concrete honest model, `All` vocabulary, with the
zero-point slot in *operator* form (`All.FarResidOp`) so that the two regimes of the density are
fed by the sharp (`All.farZPWin`, `ρ ≥ μ/10`) and the crude (`All.farZPGen`, all `ρ ≥ 0`) slots.

* `farLegCore` — the shared final bookkeeping.
* `RB5FSAllKHonest_asm` — the target `RB5FSAllK` at the honest family.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The universal constant of the `χ⋆χ` Taylor row (`All.convScale_taylor`'s witness). -/
noncomputable def Sfar : ℝ := 2 * Classical.choose Work.BoseFixB1S.conv3chi_dev_quadratic

lemma Sfar_nonneg : 0 ≤ Sfar :=
  mul_nonneg (by norm_num)
    (Classical.choose_spec Work.BoseFixB1S.conv3chi_dev_quadratic).1

/-- The diluteness threshold of the far leg: it makes `R ≤ ℓχ₀`, `100R ≤ ℓ`, the
`χ⋆χ`-mass deficit small (`Sfar(R/ℓ)² ≤ 1`) and the `fsXp` slack `10³⁰⁰X^{289/8} ≤ 10^{-100}`
hold simultaneously. -/
noncomputable def eps₀Far (v : E3 → ℝ) (R : ℝ) : ℝ :=
  min (min (10 ^ (-(4000 : ℤ)))
        ((BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ)))
      (min ((BoseGases.a v / (100 * R)) ^ (323 / 163 : ℝ))
           ((BoseGases.a v ^ 2 / ((Sfar + 1) * R ^ 2 * 10 ^ 15)) ^ (323 / 320 : ℝ)))

/-- **The shared final bookkeeping of the far leg.** -/
theorem farLegCore {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (D : KzDatum) {μ ρ K ζ ω₀ : ℝ}
    (f : D.F.H) (hf : D.T.NWindow D.E.bigM f)
    (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ) (hμ : 0 < μ)
    (hε₀ : μ * BoseGases.a v ^ 3 ≤ 10 ^ (-(4000 : ℤ)))
    (hZPop : -(((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * K) * Work.BoseFixR.farMass v h μ
          + Work.BoseFixR.ErrRes v μ ρ / 2) * D.F.normSq f
        ≤ D.F.qw f (Work.BoseBoxFock.KzBogFS D.F (Work.BoseFixR.All.farEnv D.E v μ ρ) ρ))
    (h3Q : ∀ g : D.F.H, D.T.NWindow D.E.bigM g →
        -(Work.BoseFixR.ErrRes v μ ρ / 4) * D.F.normSq g
          ≤ D.F.qw g (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (∑ k : D.Mode, (Work.BoseFixR.All.epsFar v μ ρ * D.E.tau k) • D.F.nOp k))
    (hτev : ∀ k : D.Mode, D.E.tau (-k) = D.E.tau k)
    (hτ0 : ∀ k : D.Mode, 0 ≤ D.E.tau k)
    (hε1 : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 2)
    (hwin : ∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k))
        ≤ 16 * D.E.bigM * D.F.normSq f)
    (hcorr : 16 * ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        * D.E.bigM ≤ Work.BoseFixR.ErrRes v μ ρ / 4)
    (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hω0 : 0 ≤ ω₀) (hω1 : ω₀ ≤ 16 * Real.pi * BoseGases.a v)
    (hmass : Work.BoseFixR.farMass v h μ ≤ (1 + ζ) * ω₀)
    (hE : (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀ * (K * (1 + ζ) - 1)
        ≤ 4 * BoseGases.a v * (ρ - μ) ^ 2 * (ell v μ) ^ 3)
    (hg0 : D.gHat0 = 8 * Real.pi * BoseGases.a v) (hmuE : D.E.mu = μ)
    (hellE : D.E.ell = ell v μ) (hbigME : D.E.bigM = bigMV v μ)
    (hωdef : D.E.W1omega0 = ω₀)
    (hfar : Work.BoseBoxFock.FarCondFS v μ ρ)
    (hb : 0 < D.E.b) (hell : 0 < D.E.ell) (hd : 0 < D.E.d) (heT : 0 ≤ D.E.eT)
    (hW10 : |D.E.W1 0| ≤ 16 * Real.pi * BoseGases.a v) (hMnn : 0 ≤ D.E.bigM)
    (hview : D.viewFSAll v h μ) :
    Work.BoseFixR.FarBound v μ * D.F.normSq f
      ≤ D.F.qw f (Work.BoseBoxFock.KzOpFS D.F D.T D.E D.gHat0 ρ) := by
  set Nf : ℝ := D.F.normSq f with hNfdef
  have hNf : 0 ≤ Nf := by rw [hNfdef]; exact D.F.normSq_nonneg f
  have ha : 0 < BoseGases.a v := hav
  have hℓ : 0 < ell v μ := by rw [← hellE]; exact hell
  have hMnn' : 0 ≤ Work.BoseFixR.farMass v h μ := by
    rw [Work.BoseFixR.farMass]
    exact mul_nonneg (by positivity) (integral_nonneg (fun q => by positivity))
  have hEEnn : 0 ≤ Work.BoseFixR.ErrRes v μ ρ :=
    Work.BoseFixR.ErrRes_nonneg hμ ha hρ hℓ.le
  have hCnn : 0 ≤ (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * K :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ρ)) (pow_nonneg hℓ.le 3)) hK
  -- ## 1. the residual (operator zero-point slot)
  have hres := farResidOp (v := v) D f hf hav hρ hZPop h3Q hτev hτ0 hε1 hwin hcorr
    (mul_nonneg hCnn hMnn') hEEnn
  have hres' : -(Work.BoseFixR.ErrRes v μ ρ) * Nf
      ≤ ((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * K) * Work.BoseFixR.farMass v h μ * Nf
        + D.F.qw f (Work.BoseBoxFock.KzBogFS D.F D.E ρ)
        + D.F.qw f (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ))
        + D.F.qw f (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))
        + D.F.qw f (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)) := by
    have h' := hres
    rw [← hNfdef] at h'
    linarith [h']
  -- ## 2. the slots
  have hgap := gap_slot (v := v) (h := h) (μ := μ) D hb hell hd heT f
  have hnplus := nPlus_slot (v := v) (h := h) (μ := μ) D hav hview hW10 hMnn ρ f hf
  have hnplus' : -((|ρ - μ| * (16 * Real.pi * BoseGases.a v) * 16) * D.E.bigM) * Nf
      ≤ ((ρ - μ) * D.E.W1 0) * D.F.qw f (∑ k : D.Mode, D.F.nOp k) := by
    have h' := hnplus
    rw [← hNfdef, FockData.qw_smul] at h'
    nlinarith [h']
  have hcnum := cnum_slot_split (v := v) (h := h) (μ := μ) (ρ := ρ) D hav hg0 hmuE hellE f
  -- ## 3. the coefficient arithmetic
  have hCextra : ((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * K) * Work.BoseFixR.farMass v h μ
        - (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀
      ≤ (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀ * (K * (1 + ζ) - 1) := by
    have h1 : (0 : ℝ) ≤ (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ρ)) (pow_nonneg hℓ.le 3)) hω0
    nlinarith [hmass, hCnn, h1, hK, hζ, hω0, mul_nonneg hK h1, mul_nonneg hζ h1]
  have hcontra : Work.BoseFixR.ErrRes v μ ρ
        + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * bigMV v μ)
        + Work.BoseFixR.errLHY v μ
        + (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀ * (K * (1 + ζ) - 1)
      ≤ 4 * Real.pi * BoseGases.a v * (ρ - μ) ^ 2 * (ell v μ) ^ 3 := by
    have ht0 : 0 < dil v μ := by rw [dil]; positivity
    have ht1 : dil v μ ≤ 1 := by
      rw [dil]
      exact le_trans hε₀ (by
        rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num, one_div]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)))
    have hcl : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [closeThreshold, Kl_inv_sq v hμ hav]
    have hX3 : (fsX v μ) ^ 3 = (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [fsX, Work.BoseBox.fsXp, ← Real.rpow_natCast (dil v μ ^ (1 / 323 : ℝ)) 3,
        ← Real.rpow_mul ht0.le]
      congr 1
      norm_num
    have hfarFS : Work.BoseBoxFock.closeThresholdFS v μ ≤ |ρ - μ| := hfar
    have hfarX : μ * (fsX v μ) ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by
      have hmul := mul_le_mul_of_nonneg_right hfarFS
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi)
      have h1 : closeThreshold v μ ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by
        rw [Work.BoseBoxFock.closeThresholdFS] at hmul
        calc closeThreshold v μ
            = ((2 : ℝ) ^ 14 * Real.pi) * Work.BoseBoxFock.closeThresholdFS v μ :=
              Work.BoseFixR.closeThreshold_eq_mul_closeThresholdFS v μ
          _ = Work.BoseBoxFock.closeThresholdFS v μ * ((2 : ℝ) ^ 14 * Real.pi) := by ring
          _ ≤ |ρ - μ| * ((2 : ℝ) ^ 14 * Real.pi) := hmul
          _ = (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by ring
      rw [hX3, ← hcl]
      exact h1
    have hX0 : 0 < fsX v μ := by
      rw [fsX, Work.BoseBox.fsXp]
      exact Real.rpow_pos_of_pos ht0 _
    have hX1 : fsX v μ ≤ 1 := by
      rw [fsX, Work.BoseBox.fsXp]
      calc (dil v μ) ^ (1 / 323 : ℝ) ≤ 1 ^ (1 / 323 : ℝ) :=
            Real.rpow_le_rpow ht0.le ht1 (by norm_num)
        _ = 1 := by norm_num
    have hML : bigMV v μ = (fsX v μ) ^ (337 / 4 : ℝ) * (μ * (ell v μ) ^ 3) :=
      BigMVRatio hav hμ
    have hM0 : 0 < bigMV v μ := by rw [hML]; positivity
    have hslack : (10 : ℝ) ^ 300 * (fsX v μ) ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)) := by
      have hb : (fsX v μ) ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(400 : ℤ)) :=
        FsXPowBound hav hμ (by rw [dil]; exact hε₀)
      calc (10 : ℝ) ^ 300 * (fsX v μ) ^ (289 / 8 : ℝ)
          ≤ (10 : ℝ) ^ 300 * (10 : ℝ) ^ (-(400 : ℤ)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (10 : ℝ) ^ (-(100 : ℤ)) := by field_simp
    have hFA := farArithExtra (A := BoseGases.a v) (μ := μ) (ρ := ρ) (L := ell v μ)
      (M := bigMV v μ) (X := fsX v μ)
      (E := (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀ * (K * (1 + ζ) - 1))
      hav hμ hρ hℓ hM0 hX0 hX1 hfarX hML hslack hE
    have h1 : Work.BoseFixR.ErrRes v μ ρ
        = 10 ^ 300 * ((ρ + μ) * BoseGases.a v * bigMV v μ
            + (ρ + μ) ^ (3 / 2 : ℝ) * BoseGases.a v
                * Real.sqrt ((ell v μ) ^ 3 * bigMV v μ)) := by
      rw [Work.BoseFixR.ErrRes]
    have h2 : Work.BoseFixR.errLHY v μ
        = 8 * Real.pi * Work.UBB.lhyC * μ ^ 2 * BoseGases.a v * (ell v μ) ^ 3
            * (fsX v μ) ^ (323 / 2 : ℝ) := by
      rw [Work.BoseFixR.errLHY, Work.BoseFixR.ell3,
        Work.BoseFixR.sqrt_dil_eq_fsX_rpow hμ hav]
    have h3 : |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * bigMV v μ)
        = |ρ - μ| * (256 * Real.pi * BoseGases.a v * bigMV v μ) := by ring
    rw [h1, h2, h3]
    linarith [hFA]
  -- ## 4. the final assembly
  have hmain : Work.BoseFixR.ErrRes v μ ρ
        + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * bigMV v μ)
        + Work.BoseFixR.errLHY v μ
        + (((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * K) * Work.BoseFixR.farMass v h μ
            - (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀)
      ≤ 4 * Real.pi * BoseGases.a v * (ρ - μ) ^ 2 * (ell v μ) ^ 3 := by
    linarith [hcontra, hCextra]
  have hcoefN := mul_le_mul_of_nonneg_right hmain hNf
  have hBeq : (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
          + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0 + (1 / 2) * ρ ^ 2 * D.E.W1omega0)) * D.F.normSq f
      = (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
            + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0)) * D.F.normSq f
        + ((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * ω₀) * D.F.normSq f := by
    rw [hmuE, hellE, hωdef, hg0]
    ring
  -- align the slot statements with the goal's vocabulary
  rw [hellE] at hgap
  rw [hg0, hmuE, hellE] at hcnum
  rw [← hNfdef] at hcnum
  rw [errLHY_eq_FarBound, KzOpFS_qw_decomp]
  rw [Work.BoseFixR.ell3]
  rw [hmuE, hellE, hg0, hωdef, ← hNfdef]
  rw [hbigME] at hnplus'
  rw [hmuE, hellE, hωdef, hg0, ← hNfdef] at hBeq
  linarith [hgap, hnplus', hres', hcnum, hBeq, hcoefN]

/-- **The far leg of FS §9 at the honest family**: `RB5FSAllK` for `HonestBoxFam`. -/
theorem RB5FSAllKHonest_asm {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) :
    Work.BoseBoxFock.RB5FSAllK v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) := by
  refine ⟨eps₀Far v R, ?_, ?_⟩
  · -- positivity of the threshold
    rw [eps₀Far]
    refine lt_min (lt_min (by norm_num) ?_) (lt_min ?_ ?_)
    · exact Real.rpow_pos_of_pos
        (div_pos (mul_pos hav Submission.BoseGases.chiR0_pos) hR) _
    · exact Real.rpow_pos_of_pos (div_pos hav (by positivity)) _
    · refine Real.rpow_pos_of_pos (div_pos (pow_pos hav 2) ?_) _
      exact mul_pos (mul_pos (by linarith [Sfar_nonneg] : (0 : ℝ) < Sfar + 1)
        (pow_pos hR 2)) (by norm_num)
  · intro μ hAdm hview ρ hρ hfar f hf
    obtain ⟨hμ, ht, hparams⟩ := hAdm
    have hAdmε : Work.BoseBoxFix.Adm v (eps₀Far v R) μ := ⟨hμ, ht, hparams⟩
    have hAdm' : Work.BoseBoxFix.Adm v (μ * BoseGases.a v ^ 3) μ := ⟨hμ, le_rfl, hparams⟩
    have hεA : eps₀Far v R ≤ 10 ^ (-(4000 : ℤ)) := by
      rw [eps₀Far]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hεR : eps₀Far v R
        ≤ (BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) := by
      rw [eps₀Far]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hεreg : eps₀Far v R ≤ (BoseGases.a v / (100 * R)) ^ (323 / 163 : ℝ) := by
      rw [eps₀Far]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hεS : eps₀Far v R
        ≤ (BoseGases.a v ^ 2 / ((Sfar + 1) * R ^ 2 * 10 ^ 15)) ^ (323 / 320 : ℝ) := by
      rw [eps₀Far]; exact (min_le_right _ _).trans (min_le_right _ _)
    have hε₁ : eps₀Far v R ≤ 1 := le_trans hεA (by
      rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num, one_div]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)))
    have hdil : μ * BoseGases.a v ^ 3 ≤ 10 ^ (-(4000 : ℤ)) := le_trans ht hεA
    have hRℓ := adm_R_le_ell_chiR0 (v := v) (R := R) (ε₀ := μ * BoseGases.a v ^ 3) (μ := μ)
      hR hav (le_trans ht hεR) hAdm'
    have hreg := adm_100R_le_ell (v := v) (R := R) (ε₀ := μ * BoseGases.a v ^ 3) (μ := μ)
      hR hav (le_trans ht hεreg) hAdm'
    obtain ⟨hg0, hmuE, hellE, hbigME, hbpos, hMnn, hW1o0, hellpos, hdpos, heTnn⟩ :=
      honest_view_basics (h := h) (fc := fc) (fu := fu) (HM := HM) hview
    obtain ⟨hW1, hW1o, hchi, hchiSq2, hNfL⟩ :=
      FarKernelRowsB h hv hv1 hvrad hR hv_supp hav fc fu HM hμ hview hRℓ
    have h3Q := FarThreeQFixB h hv hv1 hvrad hR hv_supp hav fc fu HM hεA hAdmε hview hRℓ
      hW1 hW1o hchi hchiSq2 hNfL ρ hρ hfar
    have hτev : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau (-k)
          = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => honestBoxFam_tau_even k
    have hτ0 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => farEnvPos_tau_nonneg _ hview k
    have hε8 : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
      FarResidBaux.epsFar_le_inv_eight hAdmε hεA hav hρ hfar
    have hε1 : epsFar v μ ρ ≤ 1 / 2 := le_trans hε8 (by norm_num)
    have hwin := window_nplus_le _ hview f hf
    have hcorr : 16 * ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
        ≤ ErrRes v μ ρ / 4 := by
      rw [hbigME]; exact FarCorrSlotB hav hμ hρ
    have hωle : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
        ≤ 16 * Real.pi * BoseGases.a v :=
      le_trans (le_abs_self _)
        (honest_W1omega0_abs_le hv hvrad hR hv_supp hav fc fu HM hview hRℓ)
    -- the mass deficit
    have hIntW : MeasureTheory.Integrable (W1fun v h (ell v μ)) := by
      rw [W1fun_eq_wScaled]
      exact wScaled_g0_integrable hR hv_supp h hellpos hRℓ
    have hIntω : MeasureTheory.Integrable (W1omegaFun v h (ell v μ)) :=
      (w1omegaFun_rows hR hellpos hv hvrad hv_supp h hRℓ).1
    have hWωpin : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
        = Work.BoseFixR.chat (W1omegaFun v h (ell v μ)) 0 := by
      unfold KzDatum.viewFSAll RViewFSAll at hview
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpin, -, -, -, -, -, -⟩ := hview
      exact hpin
    have hωeq : (∫ x, W1omegaFun v h (ell v μ) x)
        = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
      rw [← Work.BoseB7AK.W1low.chat_zero (W1omegaFun v h (ell v μ)), hWωpin]
    have hmass : Work.BoseFixR.farMass v h μ
        ≤ (1 + Sfar * (R / ell v μ) ^ 2)
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
      have hmd := massDeficitFar (h := h) (R := R) (ℓ := ell v μ) hv hvrad hR hellpos
        hv_supp hRℓ hIntW
      rw [hωeq] at hmd
      rw [Sfar]
      exact hmd
    have hζnn : 0 ≤ Sfar * (R / ell v μ) ^ 2 :=
      mul_nonneg Sfar_nonneg (sq_nonneg _)
    by_cases hρμ : μ ≤ 10 * ρ
    · -- ## the regime `ρ ≥ μ/10`: the sharp zero-point slot
      have hρpos : 0 < ρ := by linarith
      have hτrow := farTauRowMid h hv hvrad hR hv_supp hav fc fu HM hεA hAdmε hRℓ hreg ρ hρpos
        hρμ hfar
      have hZP := farZPWin h hv hv1 hvrad hR hv_supp hav fc fu HM hεA hAdmε hview hRℓ hreg
        hW1 hchi ρ hρ hfar hτrow f hf
      have hKA : 0 ≤ (1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ)) :=
        mul_nonneg (by positivity) (by positivity)
      have hZPop : -(((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))))
            * Work.BoseFixR.farMass v h μ
            + ErrRes v μ ρ / 2) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
          ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
              (Work.BoseBoxFock.KzBogFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ) := by
        have h' := hZP
        rw [show (((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
                * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))))
              * Work.BoseFixR.farMass v h μ)
            = (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
                * (((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ)))
                  * Work.BoseFixR.farMass v h μ) by ring]
        exact h'
      have hE := extraLeA (S := Sfar) (g := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
        hAdmε hεA hav hR hρ hfar Sfar_nonneg hεS hW1o0 hωle
      refine farLegCore (h := h) (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ)
        (K := (1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ)))
        (ζ := Sfar * (R / ell v μ) ^ 2)
        (ω₀ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
        f hf hav hρ hμ hdil hZPop h3Q hτev hτ0 hε1 hwin hcorr hKA hζnn hW1o0 hωle hmass
        ?_ hg0 hmuE hellE hbigME rfl hfar hbpos hellpos hdpos heTnn (hW1 0) hMnn hview
      simpa only [mul_one] using hE
    · -- ## the regime `ρ < μ/10`: the crude zero-point slot
      have hρμ' : 10 * ρ ≤ μ := le_of_lt (lt_of_not_ge hρμ)
      have hW1ae : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (E3))]
          W1fun v h (ell v μ) := by
        rw [W1fun_eq_wScaled]
        exact wScaled_g0_nonneg_ae (ℓ := ell v μ) hR hv hvrad hv_supp h
      have hSharp := sharpRowLabNAe h hv hvrad hR hellpos hv_supp hRℓ hreg hIntW hW1ae
        (HM μ).N
      have hkm : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k
            = Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k := by
        intro k
        have h1 : Work.BoseBoxFock.ellH v μ = ell v μ := honest_ellH_eq hellpos
        rw [show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k
            = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k from rfl, h1]
      have hW1pin : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k
            = Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (ell v μ) (HM μ).N)
                (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)
              * Work.BoseFixR.chat (W1fun v h (ell v μ))
                (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k) :=
        fun k => honestE_W1 h fc fu HM hellpos k
      have hLat : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
              / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
          ≤ 1 * (ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
        have hstep : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
                / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
            ≤ (1 / 2) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
                (Work.BoseFixR.chat (W1fun v h (ell v μ))
                    (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
                  / ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [hkm k, hW1pin k]
          have hcut : |Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (ell v μ) (HM μ).N)
              (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)| ≤ 1 := by
            rw [Work.BoseBoxFock.uvCut]
            exact abs_le.mpr ⟨by
              linarith [Work.BoseBoxFix.LowCut.nonneg fu
                (‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖
                  / Work.BoseBoxFock.uvRad (ell v μ) (HM μ).N)],
              Work.BoseBoxFix.LowCut.le_one fu _⟩
          rw [mul_pow]
          have h2 : (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (ell v μ) (HM μ).N)
              (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2 ≤ 1 := by
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) hcut
          have h3 : (0 : ℝ) ≤ 2 * ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2 := by
            positivity
          calc (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (ell v μ) (HM μ).N)
                (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
              * (Work.BoseFixR.chat (W1fun v h (ell v μ))
                  (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
                / (2 * ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2)
              ≤ 1 * (Work.BoseFixR.chat (W1fun v h (ell v μ))
                  (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
                / (2 * ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2) := by
                apply div_le_div_of_nonneg_right _ h3
                exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
            _ = (1 / 2) * ((Work.BoseFixR.chat (W1fun v h (ell v μ))
                  (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
                / ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2) := by ring
        calc (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
                / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
            = (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).erase 0,
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
                  / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2)) := rfl
          _ ≤ (1 / 2) * ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).erase 0,
                (Work.BoseFixR.chat (W1fun v h (ell v μ))
                    (Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k)) ^ 2
                  / ‖Work.BoseBoxFock.kmomLab (ell v μ) (HM μ).N k‖ ^ 2 := hstep
          _ ≤ (1 / 2) * (2 * ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
                * ∫ q : E3, (Work.BoseFixR.chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact hSharp
          _ = 1 * (ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
                rw [Work.BoseFixR.farMass]; ring
      have hZP := farZPGen h hv hv1 hvrad hR hv_supp hav fc fu HM hεA hAdmε hview hRℓ hW1 hchi
        1 (by norm_num) hLat ρ hρ hfar f hf
      have hZPop : -(((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3 * 2) * Work.BoseFixR.farMass v h μ
            + ErrRes v μ ρ / 2) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
          ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
              (Work.BoseBoxFock.KzBogFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ) := by
        have h' := hZP
        simp only [Work.BoseFixR.farMass] at h' ⊢
        linarith [h']
      have hζ1 := zetaLeOne (v := v) (R := R) (ε₀ := eps₀Far v R) (μ := μ) (S := Sfar)
        hR hav Sfar_nonneg hε₁ hεS hAdmε
      have hE := extraLeB (S := Sfar) (g := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
        hav hμ hρ hρμ' Sfar_nonneg hW1o0 hωle hζ1
      refine farLegCore (h := h) (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ)
        (K := 2) (ζ := Sfar * (R / ell v μ) ^ 2)
        (ω₀ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
        f hf hav hρ hμ hdil hZPop h3Q hτev hτ0 hε1 hwin hcorr ?_ hζnn hW1o0 hωle hmass
        ?_ hg0 hmuE hellE hbigME rfl hfar hbpos hellpos hdpos heTnn (hW1 0) hMnn hview
      · norm_num
      · simpa only [mul_one] using hE

end Work.BoseFixR.All
