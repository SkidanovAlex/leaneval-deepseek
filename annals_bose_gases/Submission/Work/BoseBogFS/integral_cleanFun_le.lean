import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBogFS.beta_dominance
import Submission.Work.BoseBogFS.bogGeomRows
import Submission.Work.BoseBogFS.honestFsI1Regime
import Submission.Work.BoseBogFS.integrable_fsI1Integrand
import Submission.Work.BoseBogFS.integrable_psiSc_of_cleanFun
import Submission.Work.BoseBogFS.lhyEps_le_errSlot_abs
import Submission.Work.BoseBogFS.psiSc_bulk_integral_le
import Submission.Work.BoseBogFS.psiSc_smallBall_le
import Submission.Work.BoseBogFS.psiSc_tail_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Abbreviations -/

private abbrev Fq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R ρ μ : ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun t => Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t

private abbrev Ev (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ) : ℝ :=
  Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ

private abbrev Reg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R ρ μ : ℝ) : Prop :=
  Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
    (_root_.BoseGases.a v) R ρ μ
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d

/-- `nrm t.ofLp = ‖t‖`. -/
private lemma nrm_ofLp_eq_norm (t : EuclideanSpace ℝ (Fin 3)) : Work.BoseB6Est.nrm t.ofLp = ‖t‖ := by
  rw [Work.BoseB6Est.nrm, Work.BoseBox.eucNorm3_eq_norm, WithLp.toLp_ofLp]


/-- Generic arithmetic of the error row: if `A ≤ 4B`, `E ≤ Cc·S` and the constant
comparison holds, then the whole error row is bounded. -/
private lemma errRow_arith {A B E S P K Cc : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hK : 0 ≤ K) (hCc : 0 ≤ Cc) (hAB : A ≤ 4 * B) (hES : E ≤ Cc * S)
    (hc : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cc * K ≤ 10 ^ 6 * (Cc + 1) * (K + 1)) :
    (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * A * (K * E)
      ≤ 10 ^ 6 * (Cc + 1) * (K + 1) * (B * P * S) := by
  have h16 : (0 : ℝ) ≤ (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ :=
    mul_nonneg (by norm_num) (by positivity)
  have hcle : (0 : ℝ) ≤ (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (K * E) :=
    mul_nonneg (mul_nonneg h16 hP) (mul_nonneg hK hE)
  have hstep1 : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * A * (K * E)
      ≤ (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * E) := by
    rw [show (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * A * (K * E)
          = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (K * E)) * A from by ring,
      show (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * E)
          = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (K * E)) * (4 * B) from by ring]
    exact mul_le_mul_of_nonneg_left hAB hcle
  have hstep2 : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * E)
      ≤ (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * (Cc * S)) := by
    rw [show (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * E)
          = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B)) * (K * E) from by ring,
      show (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * (Cc * S))
          = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B)) * (K * (Cc * S)) from by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hES hK)
      (mul_nonneg (mul_nonneg h16 hP) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB))
  have hstep3 : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * P * (4 * B) * (K * (Cc * S))
      = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cc * K) * (B * P * S) := by ring
  have hstep4 : ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cc * K) * (B * P * S)
      ≤ (10 ^ 6 * (Cc + 1) * (K + 1)) * (B * P * S) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg hB hP) hS)
  linarith [hstep1, hstep2, hstep3.le, hstep3.ge, hstep4]

/-! ## The target -/

theorem integral_cleanFun_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) =>
            Work.BoseBogFS.cleanFun v h ρ μ k) →
          (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
              * (∫ k : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.cleanFun v h ρ μ k))
            ≤ -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseFixR.ell v μ) ^ 3 * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              + C * Work.BoseBogFS.errBracket v R μ := by
  obtain ⟨Ct, hCt0, rowTail⟩ := psiSc_tail_integral_le
  obtain ⟨Cb, hCb0, rowBulk⟩ := psiSc_bulk_integral_le
  obtain ⟨Cs, hCs0, rowSmall⟩ := psiSc_smallBall_le
  obtain ⟨Cε, hCε0, hErrSlot⟩ := lhyEps_le_errSlot_abs
  refine ⟨10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1), by positivity, ?_⟩
  intro v h R hR hv hvrad hsupp hav
  obtain ⟨e1, he1, r1⟩ := honestFsI1Regime hR hav
  obtain ⟨e2, he2, r2⟩ := bogGeomRows hR hav
  obtain ⟨e3, he3, r3⟩ := beta_dominance hR hav
  have he4 : 0 < coreBound v R := coreBound_pos hR hav
  refine ⟨min (min e1 e2) (min e3 (coreBound v R)),
    lt_min (lt_min he1 he2) (lt_min he3 he4), ?_⟩
  intro μ hAdm ρ hclose hint
  have hE1 : min (min e1 e2) (min e3 (coreBound v R)) ≤ e1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hE2 : min (min e1 e2) (min e3 (coreBound v R)) ≤ e2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hE3 : min (min e1 e2) (min e3 (coreBound v R)) ≤ e3 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hEc : min (min e1 e2) (min e3 (coreBound v R)) ≤ coreBound v R :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hAdm1 : Work.BoseBoxFix.Adm v e1 μ := adm_mono hE1 hAdm
  have hAdm2 : Work.BoseBoxFix.Adm v e2 μ := adm_mono hE2 hAdm
  have hAdm3 : Work.BoseBoxFix.Adm v e3 μ := adm_mono hE3 hAdm
  have hcore : Core v R μ ρ :=
    core_bounds hR hav hEc μ ρ hAdm.1 hAdm.2.1 hclose
  have hreg : Reg v R ρ μ := r1 μ hAdm1 ρ hclose
  obtain ⟨hℓpos, hrl, hconv, hcond⟩ := r2 μ hAdm2 ρ hclose
  have hbeta := r3 μ hAdm3 ρ hclose
  have hμ0 : 0 < μ := hAdm.1
  have hρ0 : 0 < ρ := hcore.hρ0
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ0 hav
  have hD1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := hcore.hD1
  have hintψ : MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t) :=
    integrable_psiSc_of_cleanFun hP (Submission.BoseGases.wScaled_g0_integrable hR hsupp h hℓpos hrl) hint
  have hintF : MeasureTheory.Integrable (Fq v h R ρ μ) :=
    integrable_fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
      hreg.hε0 (by linarith [hreg.hε1])
  -- numeric side rows
  have h4c1T : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ Work.BoseBogFS.bogT v R μ := by
    have hc1 := bogC1_eq_dil v ρ μ hav hμ0 hρ0 hcore.hD0
    have hsqrt : Real.sqrt (μ / ρ) ≤ 2 := hcore.hρsqrt
    have hDpow : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) ≤ 1 :=
      Real.rpow_le_one hcore.hD0.le hcore.hD1 (by norm_num)
    have hc1le : Work.BoseBogFS.bogC1 v ρ μ ≤ 1 := by
      rw [hc1]
      nlinarith [hsqrt, hDpow, Real.sqrt_nonneg (μ / ρ)]
    have hT : 10 ^ 6 / 4 ≤ Work.BoseBogFS.bogT v R μ := hcore.hTlow
    linarith
  have hP52 : (ρ * _root_.BoseGases.a v) ^ (5 / 2 : ℝ)
      = ρ ^ 2 * _root_.BoseGases.a v
        * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) := by
    have h1 : (ρ * _root_.BoseGases.a v) ^ (5 / 2 : ℝ)
        = ρ ^ 2 * _root_.BoseGases.a v ^ 2 * Real.sqrt (ρ * _root_.BoseGases.a v) := by
      rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (mul_pos hρ0 hav),
        Real.rpow_two, ← Real.sqrt_eq_rpow]
      ring
    have h2 : Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3)
        = Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v := by
      rw [show ρ * _root_.BoseGases.a v ^ 3
            = (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v ^ 2 from by ring,
        Real.sqrt_mul (mul_nonneg hρ0.le hav.le), Real.sqrt_sq hav.le]
    rw [h1, h2]
    ring
  have hρrpow : ρ ^ 2 * _root_.BoseGases.a v
        * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3)
      ≤ 4 * (μ ^ 2 * _root_.BoseGases.a v
        * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) := by
    have h1 : ρ ^ 2 ≤ (11 / 10 * μ) ^ 2 := pow_le_pow_left₀ hρ0.le hcore.hρhi 2
    have h2 : Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3)
        ≤ Real.sqrt (11 / 10) * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 11 / 10)]
      apply Real.sqrt_le_sqrt
      rw [show (11 / 10 : ℝ) * (μ * _root_.BoseGases.a v ^ 3)
          = (11 / 10 * μ) * _root_.BoseGases.a v ^ 3 from by ring]
      exact mul_le_mul_of_nonneg_right hcore.hρhi (by positivity)
    have h3 : (11 / 10 : ℝ) ^ 2 * Real.sqrt (11 / 10) ≤ 4 := by
      have hs : Real.sqrt (11 / 10) ≤ 2 := by
        have h2 : Real.sqrt (11 / 10) ^ 2 = 11 / 10 := Real.sq_sqrt (by norm_num)
        nlinarith [h2, Real.sqrt_nonneg (11 / 10 : ℝ)]
      have h := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ (11 / 10) ^ 2)
      linarith
    have hsa : (0 : ℝ) ≤ _root_.BoseGases.a v := hav.le
    have hA : ρ ^ 2 * _root_.BoseGases.a v ≤ (11 / 10 * μ) ^ 2 * _root_.BoseGases.a v :=
      mul_le_mul_of_nonneg_right h1 hsa
    have hB : ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3)
        ≤ ((11 / 10 * μ) ^ 2 * _root_.BoseGases.a v)
          * (Real.sqrt (11 / 10) * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) :=
      mul_le_mul hA h2 (Real.sqrt_nonneg _) (by positivity)
    have hC : ((11 / 10 * μ) ^ 2 * _root_.BoseGases.a v)
          * (Real.sqrt (11 / 10) * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        = ((11 / 10 : ℝ) ^ 2 * Real.sqrt (11 / 10))
          * (μ ^ 2 * _root_.BoseGases.a v * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) := by
      ring
    have hD : ((11 / 10 : ℝ) ^ 2 * Real.sqrt (11 / 10))
          * (μ ^ 2 * _root_.BoseGases.a v * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        ≤ 4 * (μ ^ 2 * _root_.BoseGases.a v * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    exact le_trans hB (le_trans (le_of_eq hC) hD)
  -- sets
  have hSmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hAmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hCmeas : MeasurableSet
      {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧ ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter hSmeas
  have hAC : ({t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ} : Set (EuclideanSpace ℝ (Fin 3)))
        ∪ {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧
            ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}
      = {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} := by
    ext t
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨-, h2⟩)
      · exact le_trans h h4c1T
      · exact h2
    · intro ht
      rcases le_or_gt ‖t‖ (4 * Work.BoseBogFS.bogC1 v ρ μ) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ht⟩
  have hdisjAC : Disjoint ({t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ} : Set (EuclideanSpace ℝ (Fin 3)))
      {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧ ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h1 (not_le.mpr h2.1)
  have hcompl : ({t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ
      = {t : EuclideanSpace ℝ (Fin 3) | Work.BoseBogFS.bogT v R μ < ‖t‖} := by
    ext t
    simp [not_le]
  have hdiff_int : MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t) := hintψ.sub hintF
  have hIntA : MeasureTheory.IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t)
      {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ} volume := hdiff_int.integrableOn
  have hIntC : MeasureTheory.IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t)
      {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧
        ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} volume := hdiff_int.integrableOn
  have hunion :
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ},
          (Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t))
        + (∫ t in {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧
              ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
            (Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t))
      = ∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
          (Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t) := by
    rw [← setIntegral_union hdisjAC hCmeas hIntA hIntC, hAC]
  have hkey1 :
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}, Work.BoseBogFS.psiSc v h ρ μ t)
        + (∫ t in {t : EuclideanSpace ℝ (Fin 3) | Work.BoseBogFS.bogT v R μ < ‖t‖},
            Work.BoseBogFS.psiSc v h ρ μ t)
      = ∫ t, Work.BoseBogFS.psiSc v h ρ μ t := by
    rw [← hcompl]
    exact integral_add_compl hSmeas hintψ
  have haddS :
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}, Work.BoseBogFS.psiSc v h ρ μ t)
      = (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}, Fq v h R ρ μ t)
        + (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
            (Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t)) := by
    rw [← integral_add hintF.integrableOn hdiff_int.integrableOn]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hzero : ∀ t : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.bogT v R μ < ‖t‖ → Fq v h R ρ μ t = 0 := by
    intro t ht
    have hKT : (Work.BoseBogFS.bogKernel v R ρ μ).T < Work.BoseB6Est.nrm t.ofLp := by
      rw [Work.BoseBogFS.bogKernel_T, max_eq_right hcore.hTpos.le, nrm_ofLp_eq_norm]
      exact ht
    have hβ0 : (Work.BoseBogFS.bogKernel v R ρ μ).β (Work.BoseB6Est.nrm t.ofLp) = 0 :=
      (Work.BoseBogFS.bogKernel v R ρ μ).support _ hKT
    have hτnn : 0 ≤ Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
        (Work.BoseB6Est.nrm t.ofLp) :=
      Work.BoseB6Est.fsTau_nonneg hreg.hε0 (by linarith [hreg.hε1])
        (Submission.BoseGases.eucNorm3_nonneg t.ofLp)
    have hclean : Work.BoseB6Est.cleanBracket (Work.BoseBogFS.bogKernel v R ρ μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t = 0 := by
      rw [Work.BoseB6Est.cleanBracket, hβ0, add_zero,
        show (0 : ℝ) ^ 2 = 0 from by norm_num, sub_zero, Real.sqrt_sq hτnn, sub_self]
    change Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t = 0
    rw [Work.BoseB6Est.fsI1Integrand, hclean, hβ0]
    simp
  have hS1F :
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}, Fq v h R ρ μ t)
      = Work.BoseB6Est.fsI1 (Work.BoseBogFS.bogKernel v R ρ μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) := by
    have hsplit := integral_add_compl hSmeas hintF
    have hz : (∫ t in ({t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ,
        Fq v h R ρ μ t) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      exact hzero t (by rwa [hcompl] at ht)
    have hFrfl : (∫ t, Fq v h R ρ μ t)
        = Work.BoseB6Est.fsI1 (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) := by
      have hmp : MeasurePreserving
          (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
        PiLp.volume_preserving_toLp (Fin 3)
      rw [Work.BoseB6Est.fsI1]
      rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
        (Fq v h R ρ μ)]
    rw [hz, add_zero, hFrfl] at hsplit
    exact hsplit
  have htail := rowTail (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
    hR hav hv hvrad hsupp hcore hreg hrl hcond hconv hintψ
  have hrowS := rowSmall (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
    hR hav hv hvrad hsupp hcore hreg hrl hcond hconv hintψ hintF
  have hrowB := rowBulk (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
    hR hav hv hvrad hsupp hcore hreg hrl hcond hconv hbeta hintψ hintF
  have hpsi :
      (∫ t, Work.BoseBogFS.psiSc v h ρ μ t)
        ≤ -Work.BoseB6.lhyValue (8 * Real.pi) + (10 ^ 6 + (Cb + Cs) + Ct) * Ev v R μ := by
    have hcomp :
        (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
            (Work.BoseBogFS.psiSc v h ρ μ t - Fq v h R ρ μ t)) ≤ (Cb + Cs) * Ev v R μ := by
      rw [← hunion]
      linarith [hrowS, hrowB]
    have hSb :
        (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ}, Work.BoseBogFS.psiSc v h ρ μ t)
        ≤ Work.BoseB6Est.fsI1 (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
          + (Cb + Cs) * Ev v R μ := by
      rw [haddS, hS1F]
      linarith [hcomp]
    have hFS := Work.BoseB6Est.fsI1_le (h := hreg)
    rw [← hkey1]
    have h1 : (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
          Work.BoseBogFS.psiSc v h ρ μ t)
        + (∫ t in {t : EuclideanSpace ℝ (Fin 3) | Work.BoseBogFS.bogT v R μ < ‖t‖},
            Work.BoseBogFS.psiSc v h ρ μ t)
        ≤ (Work.BoseB6Est.fsI1 (Work.BoseBogFS.bogKernel v R ρ μ)
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
            + (Cb + Cs) * Ev v R μ) + Ct * Ev v R μ := add_le_add hSb htail
    have h2 : (Work.BoseB6Est.fsI1 (Work.BoseBogFS.bogKernel v R ρ μ)
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
            + (Cb + Cs) * Ev v R μ) + Ct * Ev v R μ
        ≤ (-Work.BoseB6.lhyValue (8 * Real.pi) + 10 ^ 6 * Ev v R μ)
            + (Cb + Cs) * Ev v R μ + Ct * Ev v R μ := by
      linarith [hFS]
    have h3 : (-Work.BoseB6.lhyValue (8 * Real.pi) + 10 ^ 6 * Ev v R μ)
            + (Cb + Cs) * Ev v R μ + Ct * Ev v R μ
        = -Work.BoseB6.lhyValue (8 * Real.pi) + (10 ^ 6 + (Cb + Cs) + Ct) * Ev v R μ := by
      ring
    linarith [h1, h2, h3]
  have herr0 : (0 : ℝ) ≤ Work.BoseBogFS.errSlot v R μ := by
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.errExp_eq]
    have h1 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) := by
      positivity
    have h3 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ (1 / 1615 : ℝ) :=
      Real.rpow_nonneg hcore.hD0.le _
    linarith
  have hSa : (0 : ℝ) ≤ _root_.BoseGases.a v := hav.le
  have hEv0 : (0 : ℝ) ≤ Ev v R μ := Work.BoseB6Est.FsI1Regime.lhyEps_nonneg hreg
  have hρa0 : (0 : ℝ) ≤ ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg ρ) hSa) (Real.sqrt_nonneg _)
  have hμa0 : (0 : ℝ) ≤ μ ^ 2 * _root_.BoseGases.a v
      * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg μ) hSa) (Real.sqrt_nonneg _)
  have hK0 : (0 : ℝ) ≤ 10 ^ 6 + (Cb + Cs) + Ct := by linarith
  have hCε0' : (0 : ℝ) ≤ Cε := hCε0
  have herr1 : Ev v R μ ≤ Cε * Work.BoseBogFS.errSlot v R μ := hErrSlot hR hav hμ0 hD1
  have hfac : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 ≤ 1 := by
    have hpos : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
    have hpi2 : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hbig : (2 : ℝ) ≤ (2 * Real.pi) ^ 3 :=
      le_trans (by norm_num : (2 : ℝ) ≤ (2 : ℝ) ^ 3) (pow_le_pow_left₀ (by norm_num) hpi2 3)
    rw [show (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 = 2 * ((2 * Real.pi) ^ 3)⁻¹ by ring,
      ← div_eq_mul_inv, div_le_one hpos]
    exact hbig
  have hc : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cε * (10 ^ 6 + (Cb + Cs) + Ct)
      ≤ 10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1) := by
    have h1 : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cε ≤ 1 * Cε :=
      mul_le_mul_of_nonneg_right hfac hCε0'
    have h2 : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * 4 * Cε * (10 ^ 6 + (Cb + Cs) + Ct)
        ≤ 1 * Cε * (10 ^ 6 + (Cb + Cs) + Ct) :=
      mul_le_mul_of_nonneg_right h1 hK0
    have h3 : 1 * Cε * (10 ^ 6 + (Cb + Cs) + Ct) ≤ (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1) := by
      nlinarith [hCε0', hK0]
    have h4 : (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1)
        ≤ 10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1) := by
      have h5 : (0 : ℝ) ≤ (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [h5]
    linarith [h2, h3, h4]
  have hmain3 := errRow_arith (A := ρ ^ 2 * _root_.BoseGases.a v
        * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
      (B := μ ^ 2 * _root_.BoseGases.a v * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
      (E := Ev v R μ) (S := Work.BoseBogFS.errSlot v R μ)
      (P := (Work.BoseFixR.ell v μ) ^ 3) (K := 10 ^ 6 + (Cb + Cs) + Ct) (Cc := Cε)
      hρa0 hμa0 hEv0 herr0 (pow_nonneg hℓpos.le 3) hK0 hCε0' hρrpow herr1 hc
  have hErrRow :
      (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
        * (ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
        * ((10 ^ 6 + (Cb + Cs) + Ct) * Ev v R μ)
      ≤ (10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1))
        * Work.BoseBogFS.errBracket v R μ := by
    rw [Work.BoseBogFS.errBracket_eq_mul_errSlot v R μ]
    refine le_trans hmain3 ?_
    rw [Work.BoseFixR.dil]
    simp only [Work.BoseFixR.ell3]
    exact le_of_eq (by ring)
  have hred := (integrand_reduction (v := v) (h := h) (ρ := ρ) (μ := μ) hP).2.2
  rw [hred, hP52]
  have hgoal : (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
        * ((ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
            * (∫ t, Work.BoseBogFS.psiSc v h ρ μ t))
      ≤ -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseFixR.ell v μ) ^ 3 * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
        + (10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1))
            * Work.BoseBogFS.errBracket v R μ := by
    have hℓ30 : (0 : ℝ) ≤ (Work.BoseFixR.ell v μ) ^ 3 := pow_nonneg hℓpos.le 3
    have hc0 : (0 : ℝ) ≤ (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hℓ30
    calc (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
          * ((ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              * (∫ t, Work.BoseBogFS.psiSc v h ρ μ t))
        = ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3)
            * ((ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              * (∫ t, Work.BoseBogFS.psiSc v h ρ μ t)) := by ring
      _ ≤ ((1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3)
            * ((ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
              * (-Work.BoseB6.lhyValue (8 * Real.pi)
                  + (10 ^ 6 + (Cb + Cs) + Ct) * Ev v R μ)) := by
          apply mul_le_mul_of_nonneg_left _ hc0
          exact mul_le_mul_of_nonneg_left hpsi hρa0
      _ = -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseFixR.ell v μ) ^ 3 * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
          + (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * (ρ ^ 2 * _root_.BoseGases.a v * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
            * ((10 ^ 6 + (Cb + Cs) + Ct) * Ev v R μ) := by
          rw [← half_lhyValue_eight_pi]
          ring
      _ ≤ -(4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseFixR.ell v μ) ^ 3 * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
          + (10 ^ 6 * (Cε + 1) * (10 ^ 6 + (Cb + Cs) + Ct + 1))
              * Work.BoseBogFS.errBracket v R μ := by
          linarith [hErrRow]
  exact le_trans (le_of_eq (by ring)) hgoal

end Work.BoseBogFS
