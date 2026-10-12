import ChallengeDeps
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.All.FarResidAdm
import Submission.Work.BoseFixR.All.FarThreeQArithWide
import Submission.Work.BoseFixR.All.FarThreeQSlots
import Submission.Work.BoseFixR.All.HonTauGeHalfSq
import Submission.Work.BoseFixR.All.HonestEnvParity
import Submission.Work.BoseFixR.All.LatticeRowWide
import Submission.Work.BoseFixR.All.ccrKBesselHonest
import Submission.Work.BoseFixR.Q3TWedgeBoundV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Glue for the honest family -/

/-- `|f(s)| ≤ 1` for a low-momentum cut-off. -/
lemma lowCut_abs_le_one (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : |fc.f s| ≤ 1 := by
  rw [abs_le]
  constructor
  · by_cases h : s ≤ 2
    · have h2 : fc.f 2 = 0 := fc.zero 2 le_rfl
      have := fc.anti h
      linarith
    · rw [fc.zero s (not_le.mp h).le]
      norm_num
  · by_cases h : s ≤ 1
    · rw [fc.one s h]
    · have h1 : 1 ≤ s := (not_le.mp h).le
      have := fc.anti h1
      rwa [fc.one 1 le_rfl] at this

/-- The `Ŵ₁ω(0)` pin of the view. -/
lemma view_W1omega0_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) :
    D.E.W1omega0 = chat (W1omegaFun v h (ell v μ)) 0 := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -, -, -, -, -, -⟩ := hview
  exact hW

/-- `|Ŵ₁ω(0)| ≤ 16π·a v` at the honest family. -/
lemma honest_W1omega0_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {μ : ℝ}
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|
      ≤ 16 * Real.pi * BoseGases.a v := by
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.All.ell_pos_of_le hR hRℓ
  have hpin := view_W1omega0_eq (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hview
  rw [hpin]
  have hrows := Work.BoseFixR.All.w1omegaFun_rows (v := v) (R := R) (ℓ := Work.BoseFixR.ell v μ)
    hR hℓ hv hvrad hv_supp h (by rw [Work.BoseFixR.ell]; exact hRℓ)
  calc |chat (W1omegaFun v h (Work.BoseFixR.ell v μ)) 0|
      ≤ ∫ z, |W1omegaFun v h (Work.BoseFixR.ell v μ) z| :=
        Work.BoseB7AK.W1rows.abs_chat_le_integral_abs _
    _ ≤ 16 * Real.pi * BoseGases.a v := hrows.2

/-- `|f_L| ≤ 1` at the honest family. -/
lemma honest_fL_abs_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ : ℝ} (s : Lab (HM μ).N) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s| ≤ 1 := by
  rw [show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s
      = fLFS fc ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.mu)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat) _ from rfl]
  exact lowCut_abs_le_one fc _

/-- `Σ_s |f_L(s)| ≤ Cf` from the support-count row `hNfL`. -/
lemma honest_fL_sum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ Cf : ℝ} (hNfL : ((∑ s ∈ (excited (Lab (HM μ).N)).filter
        (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ)) ≤ Cf))
    (hCf : 0 ≤ Cf) :
    ∑ s ∈ excited (Lab (HM μ).N),
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s| ≤ Cf := by
  classical
  refine le_trans ?_ hNfL
  rw [← Finset.sum_filter_of_ne (s := excited (Lab (HM μ).N))
    (f := fun s => |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s|)
    (p := fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0) ?_]
  · exact Finset.sum_le_sum (fun s _ => honest_fL_abs_le_one s)
  · intro s _ hs
    simpa [abs_eq_zero] using hs

/-- The `ccrK` diagonal row at the honest family: `|ccrK p p| ≤ 2`. -/
lemma honest_ccrK_diag {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ : ℝ} (p : Lab (HM μ).N) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.ccrK p p| ≤ 2 := by
  have hk : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.ccrK p p
      = Work.BoseK15.corpusBox.boxKernel (Work.BoseBoxFock.ellH v μ)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p) := by
    rw [show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        = Work.BoseB4.boxFockData Work.BoseK15.corpusBox
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            (Work.BoseBoxFock.kmomLab_neg _ _) (HM μ).m (HM μ).f (HM μ).hf from rfl]
    exact Work.BoseB4.boxFockData_ccrK Work.BoseK15.corpusBox _ _ _ _ _ p p
  rw [hk]
  rw [show Work.BoseK15.corpusBox.boxKernel (Work.BoseBoxFock.ellH v μ)
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p)
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p)
      = Work.BoseK15.corpusBox.hatChiSq 0
        - Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p) ^ 2 from by
    rw [Work.BoseB4.BoxData.boxKernel]
    simp only [sub_self, smul_zero]
    ring]
  have h1 : |Work.BoseK15.corpusBox.hatChiSq 0| ≤ 1 := Work.BoseK15.hatChi_le_one.2 0
  have h2 : |Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p)| ≤ 1 :=
    Work.BoseK15.hatChi_le_one.1 _
  calc |Work.BoseK15.corpusBox.hatChiSq 0
        - Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p) ^ 2|
      ≤ |Work.BoseK15.corpusBox.hatChiSq 0|
        + |Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom p) ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := by
        refine add_le_add h1 ?_
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) h2
    _ = 2 := by norm_num

/-- **The linear-word slot (`ℓ²`-Cauchy–Schwarz against the window).** -/
lemma linOpTL2Slot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (D : KzDatum) (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hview : D.viewFSAll v h μ)
    (hW1o0 : |D.E.W1omega0| ≤ 16 * Real.pi * BoseGases.a v)
    (hchiSq2 : ∑ k ∈ excited D.Mode, (D.E.hatChiSq k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (f : D.F.H) (hf : D.T.NWindow D.E.bigM f) :
    |D.F.qw f (D.T.linOpT (KzEnvAt D.E ρ))|
      ≤ 320 * Real.pi * BoseGases.a v * ρ * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM * D.F.normSq f := by
  have hMnn : 0 ≤ D.E.bigM := view_bigM_nonneg D hview
  have hrw : (KzEnvAt D.E ρ).rho = ρ := view_rho_KzEnvAt D hμ hav hview ρ hρ
  have hval : D.T.linOpT (KzEnvAt D.E ρ)
      = (ρ * (KzEnvAt D.E ρ).z * (KzEnvAt D.E ρ).W1omega0) •
          ∑ s ∈ excited D.Mode,
            ((KzEnvAt D.E ρ).hatChiSq s) • (D.T.taDag s + D.T.ta s) := by
    rw [TildeData.linOpT, hrw]
  have hlin := NWindow_linear_bound D.F D.T hMnn hf (excited D.Mode)
    (fun s hs => by
      rw [excited, Finset.mem_erase] at hs
      exact hs.1)
    (fun s => (KzEnvAt D.E ρ).hatChiSq s)
  have hc : |ρ * (KzEnvAt D.E ρ).z * (KzEnvAt D.E ρ).W1omega0|
      ≤ 16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)) := by
    rw [show (KzEnvAt D.E ρ).W1omega0 = D.E.W1omega0 from rfl,
      show (KzEnvAt D.E ρ).z = Real.sqrt (ρ * D.E.ell ^ 3) from rfl, abs_mul]
    have hpos : 0 ≤ ρ * Real.sqrt (ρ * D.E.ell ^ 3) := mul_nonneg hρ (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hpos]
    have h2 := abs_le.mp hW1o0
    nlinarith [h2.1, h2.2, hpos, Real.pi_pos, hav.le]
  have hsq : Real.sqrt (∑ s ∈ excited D.Mode, (KzEnvAt D.E ρ).hatChiSq s ^ 2) ≤ 10 := by
    rw [show (∑ s ∈ excited D.Mode, (KzEnvAt D.E ρ).hatChiSq s ^ 2)
        = ∑ k ∈ excited D.Mode, (D.E.hatChiSq k) ^ 2 from rfl]
    have h10 : Real.sqrt 100 = 10 := by norm_num
    rw [← h10]
    exact Real.sqrt_le_sqrt hchiSq2
  have hval2 : D.F.qw f (D.T.linOpT (KzEnvAt D.E ρ))
      = (ρ * (KzEnvAt D.E ρ).z * (KzEnvAt D.E ρ).W1omega0)
          * D.F.qw f (∑ s ∈ excited D.Mode,
              ((KzEnvAt D.E ρ).hatChiSq s) • (D.T.taDag s + D.T.ta s)) := by
    rw [hval, FockData.qw, FockData.qw]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hval2, abs_mul]
  calc |ρ * (KzEnvAt D.E ρ).z * (KzEnvAt D.E ρ).W1omega0|
        * |D.F.qw f (∑ s ∈ excited D.Mode,
            (KzEnvAt D.E ρ).hatChiSq s • (D.T.taDag s + D.T.ta s))|
      ≤ (16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)))
        * (2 * Real.sqrt D.E.bigM
            * Real.sqrt (∑ s ∈ excited D.Mode, (KzEnvAt D.E ρ).hatChiSq s ^ 2)
            * D.F.normSq f) :=
          mul_le_mul hc hlin (abs_nonneg _) (by positivity)
    _ ≤ (16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)))
        * (2 * Real.sqrt D.E.bigM * 10 * D.F.normSq f) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hns : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
          have hb : 0 ≤ Real.sqrt D.E.bigM := Real.sqrt_nonneg _
          have h1 : Real.sqrt (∑ s ∈ excited D.Mode, (KzEnvAt D.E ρ).hatChiSq s ^ 2)
              * D.F.normSq f ≤ 10 * D.F.normSq f :=
            mul_le_mul_of_nonneg_right hsq hns
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * Real.sqrt D.E.bigM)
          linarith [h2]
    _ = 320 * Real.pi * BoseGases.a v * ρ * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM * D.F.normSq f := by ring

/-- The linear slot at the honest family. -/
lemma linOpT_slot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ ρ : ℝ} (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hW1o0 : |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|
      ≤ 16 * Real.pi * BoseGases.a v)
    (hchiSq2 : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
          (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))|
      ≤ 320 * Real.pi * BoseGases.a v * ρ
          * Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3)
          * Real.sqrt ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := by
  obtain ⟨-, -, hell, -, -, -, -, -, -, -⟩ := honest_view_basics hview
  have h := linOpTL2Slot (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ)
    hav hμ hview hW1o0 hchiSq2 ρ hρ f hf
  rwa [hell] at h

/-- The scalar pin `E.aScat = a v`. -/
lemma view_aScat_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) : D.E.aScat = a v := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, ha, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hview
  exact ha

/-- `(z/ℓ³)² = ρ/ℓ³` at `KzEnvAt`. -/
lemma KzEnvAt_z_div_cube_sq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) {ρ ℓ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 ≤ ρ) (hell : E.ell = ℓ) :
    ((KzEnvAt E ρ).z / (KzEnvAt E ρ).ell ^ 3) ^ 2 = ρ / ℓ ^ 3 := by
  rw [show (KzEnvAt E ρ).z = Real.sqrt (ρ * E.ell ^ 3) from rfl,
    show (KzEnvAt E ρ).ell = E.ell from rfl, hell, div_pow,
    Real.sq_sqrt (mul_nonneg hρ (pow_nonneg hℓ.le 3))]
  field_simp

/-- The far three-`Q` arithmetic: the three slot bounds plus `A+B+C ≤ Err/4` give the target. -/
lemma farArith4 {N A B C E₁ E₂ E₃ Err : ℝ} (hN : 0 ≤ N)
    (hA : -A * N ≤ E₁) (hB : -B * N ≤ E₂) (hC : -C * N ≤ E₃)
    (harith : A + B + C ≤ Err / 4) :
    -(Err / 4) * N ≤ E₁ + E₂ + E₃ := by
  nlinarith [hA, hB, hC, harith, hN]

theorem FarThreeQFixB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hW1o : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k|
          ≤ 16 * Real.pi * BoseGases.a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (hchiSq2 : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k) ^ 2 ≤ 100)
    (hNfL : ((∑ s ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -(Work.BoseFixR.ErrRes v μ ρ / 4)
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
              (Work.BoseFixR.All.epsFar v μ ρ
                  * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k)
                • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) := by
  have hμ : 0 < μ := hAdm.1
  obtain ⟨hg0, hmu, hell, hbigMpin, hb, hMnn, hW1ω0nn, hellpos, hd, heT⟩ :=
    honest_view_basics hview
  have hvE : Work.BoseB7.FSParamsView (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E := Classical.choice hview.1
  have hKH : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH := lt_of_lt_of_le zero_lt_one hvE.one_le_KH
  have haSc : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat := hvE.a_pos
  have hKLpos : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL := lt_of_lt_of_le zero_lt_one hvE.one_le_KL
  have hbigM1 : 1 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := hvE.one_le_bigM
  have hbigMpos : 0 < Work.BoseFixR.bigMV v μ := by
    rw [← hbigMpin]; linarith
  -- the `KzEnvAt` pins
  have hKASC : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).aScat = BoseGases.a v := by
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).aScat = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat from rfl, view_aScat_eq _ hview]
  have hKKH : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).KH = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH := rfl
  have hKM : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).bigM = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := rfl
  have hKFL : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).fL = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL := rfl
  have hKW1 : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).W1 = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 := rfl
  have hKT : (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau := rfl
  have hKz : ((KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).z / (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).ell ^ 3) ^ 2
      = ρ / (Work.BoseFixR.ell v μ) ^ 3 :=
    KzEnvAt_z_div_cube_sq (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E hellpos hρ hell
  -- the rows
  have hW1o0 : |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0| ≤ 16 * Real.pi * BoseGases.a v :=
    honest_W1omega0_abs_le hv hvrad hR hv_supp hav fc fu HM hview hRℓ
  have hCfnn : 0 ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3 := by
    have h1 : 0 ≤ Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1 := by
      have h2 : 0 ≤ Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) :=
        mul_nonneg (mul_nonneg (le_of_lt hellpos) (le_of_lt hKLpos)) (Real.sqrt_nonneg _)
      linarith
    exact mul_nonneg (by norm_num) (pow_nonneg h1 3)
  have hfl1 : ∀ s : Lab (HM μ).N, |(KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).fL s| ≤ 1 := by
    intro s
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).fL s = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s from rfl]
    exact honest_fL_abs_le_one s
  have hcfs : ∑ s ∈ excited (Lab (HM μ).N), |(KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).fL s|
      ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3 := by
    rw [show (∑ s ∈ excited (Lab (HM μ).N), |(KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).fL s|)
        = ∑ s ∈ excited (Lab (HM μ).N),
            |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s| from rfl]
    exact honest_fL_sum_le hNfL hCfnn
  have hW1' : ∀ k : Lab (HM μ).N, |(KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).W1 k| ≤ 16 * Real.pi * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).aScat := by
    intro k
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).W1 k = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k from rfl, hKASC]
    exact hW1 k
  have hPH' : ∀ k ∈ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ),
      1 / (2 * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).KH * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).aScat) ≤ ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ := by
    intro k hk
    rw [show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ) = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E from rfl] at hk
    exact (Finset.mem_filter.mp hk).2
  have hRowE : ∑ k ∈ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ),
      (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).W1 k ^ 2 / ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2
      ≤ 10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3 := by
    have h0 := FarRowW1sqWide (v := v) h hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hview hRℓ
    rw [show (∑ k ∈ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ),
        (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).W1 k ^ 2 / ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2)
        = ∑ k ∈ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k ^ 2
            / ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 from rfl]
    exact h0
  have hccrB : ∀ (k : Lab (HM μ).N) (c : Lab (HM μ).N → ℝ)
      (u : Lab (HM μ).N → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H),
      ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
          c s * c s' * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k))
            * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s'))
        ≤ 100 * ∑ s ∈ excited (Lab (HM μ).N),
            c s ^ 2 * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s)) :=
    ccrKBesselHonest (v := v) h hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hview hRℓ
  obtain ⟨Cn, hCn0, hCn16, hCn⟩ := honest_bessel hview
  have hnN : ∀ g : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H, ∑ p : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode, (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp p g) g ≤ 16 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N g) g := by
    intro g
    have htot : ∑ p : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode, (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp p g) g
        = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp ((∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode, (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) g) g := by
      rw [show (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) g
          = ∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k g from
        LinearMap.sum_apply Finset.univ
          (fun k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode =>
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) g]
      rw [show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
            (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k g)
          = ∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k g) from
        map_sum (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
          (fun k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode =>
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k g) Finset.univ]
      exact (LinearMap.sum_apply Finset.univ
        (fun k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode =>
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k g)) g).symm
    rw [htot]
    refine le_trans (hCn g) ?_
    have hN0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N g) g := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N_nonneg g
    nlinarith [hCn0, hCn16, hN0]
  have hτ0 : ∀ k : Lab (HM μ).N, 0 ≤ (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k := by
    intro k
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k from rfl]
    exact view_tau_nonneg (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hview k
  have hτeven : ∀ k : Lab (HM μ).N, (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau (-k) = (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k := by
    intro k
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau (-k) = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau (-k) from rfl,
      show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k from rfl]
    exact Work.BoseFixR.All.honestBoxFam_tau_even k
  have hτge : ∀ k : Lab (HM μ).N, (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PH (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).KH (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).aScat k →
      ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2 ≤ (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k := by
    intro k hk
    rw [show (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k from rfl]
    exact HonTauGeHalfSq h hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hview hRℓ k hk
  have hεpos : 0 < Work.BoseFixR.All.epsFar v μ ρ := by
    rw [Work.BoseFixR.All.epsFar]
    exact Real.sqrt_pos.mpr (div_pos hbigMpos (by
      have : 0 < (Work.BoseFixR.ell v μ) ^ 3 := pow_pos hellpos 3
      nlinarith [this, hρ, hμ]))
  -- the three slot bounds
  have hlin := linOpT_slot (ρ := ρ) hav hμ hview hW1o0 hchiSq2 ρ hρ f hf
  have hQ2 := FarQ2exSlotHonest (v := v) (h := h) hav hμ hview hW1o hW1o0 ρ hρ f hf
  have hQ2' : -(512 * Real.pi * ρ * BoseGases.a v * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
    have hq2 := hQ2
    rw [← hbigMpin] at hq2
    convert hq2 using 2 <;> ring
  have hεpos2 : 0 < Work.BoseFixR.All.epsFar v μ ρ := hεpos
  have hQ3 := Q3TWedgeBoundV2 (F := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F) (T := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T) (E := KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)
    (ε := Work.BoseFixR.All.epsFar v μ ρ)
    (Cf := 10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3)
    (Row := 10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3)
    (M := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM) f hεpos2 hCfnn (by positivity) (le_of_lt (lt_of_lt_of_le zero_lt_one hbigM1))
    haSc hKH hfl1 hcfs hW1' hPH' hRowE hccrB hnN hτ0 hτeven hτge hf
  have hQ3' : -(2 / Work.BoseFixR.All.epsFar v μ ρ * (ρ / (Work.BoseFixR.ell v μ) ^ 3)
        * ((10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3)
            * (2000 * (16 * Real.pi * BoseGases.a v
                * (2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) ^ 2
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM ^ 2)
          + 2000 * (10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM))
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
            (Work.BoseFixR.All.epsFar v μ ρ * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k) • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) := by
    have hq3 := hQ3
    rw [hKz, hKASC, hKKH] at hq3
    convert hq3 using 2 <;> ring
  -- the arithmetic
  have harith := FarThreeQArithWide (v := v) h hav fc fu HM hε₀ hAdm hview ρ hρ hfar
  have harith' : 320 * Real.pi * BoseGases.a v * ρ
          * Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3) * Real.sqrt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
      + 512 * Real.pi * ρ * BoseGases.a v * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
      + 2 / Work.BoseFixR.All.epsFar v μ ρ * (ρ / (Work.BoseFixR.ell v μ) ^ 3)
        * (10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3
            * (2000 * (16 * Real.pi * BoseGases.a v
                * (2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) ^ 2
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM ^ 2)
          + 2000 * (10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
      ≤ Work.BoseFixR.ErrRes v μ ρ / 4 := harith
  have hN : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq_nonneg f
  have hbonus : 0 ≤ ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
      * (32 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := by
    have h1 : 0 ≤ (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg hεpos.le _
    have h2 : 0 ≤ 32 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM := by linarith [le_of_lt hbigMpos]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hρ h1) hav.le) h2) hN
  have hAslot : -(320 * Real.pi * BoseGases.a v * ρ * Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3)
        * Real.sqrt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
    have hab := abs_le.mp hlin
    nlinarith [hab.1]
  have hQ2slot : -(512 * Real.pi * ρ * BoseGases.a v * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
    nlinarith [hQ2']
  have hQ3slot : -(2 / Work.BoseFixR.All.epsFar v μ ρ * (ρ / (Work.BoseFixR.ell v μ) ^ 3)
        * (10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3
            * (2000 * (16 * Real.pi * BoseGases.a v * (2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) ^ 2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM ^ 2)
          + 2000 * (10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f (∑ k : Lab (HM μ).N,
            (Work.BoseFixR.All.epsFar v μ ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k) • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) := by
    have hq3 := hQ3'
    have hsum : (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
          (Work.BoseFixR.All.epsFar v μ ρ
              * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k)
            • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k)
        = ∑ k : Lab (HM μ).N,
          (Work.BoseFixR.All.epsFar v μ ρ
              * (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ).tau k)
            • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k := rfl
    rw [hsum] at hq3
    exact hq3
  have hfin := farArith4 (N := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f)
    (A := 320 * Real.pi * BoseGases.a v * ρ * Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3)
        * Real.sqrt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
    (B := 512 * Real.pi * ρ * BoseGases.a v * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
    (C := 2 / Work.BoseFixR.All.epsFar v μ ρ * (ρ / (Work.BoseFixR.ell v μ) ^ 3)
        * (10 ^ 6 * (Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3
            * (2000 * (16 * Real.pi * BoseGases.a v * (2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) ^ 2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM ^ 2)
          + 2000 * (10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM))
    (E₁ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
    (E₂ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
    (E₃ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T (KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f (∑ k : Lab (HM μ).N,
            (Work.BoseFixR.All.epsFar v μ ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k) • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k))
    (Err := Work.BoseFixR.ErrRes v μ ρ) hN hAslot hQ2slot hQ3slot harith'
  linarith [hfin]

end Work.BoseFixR.All
