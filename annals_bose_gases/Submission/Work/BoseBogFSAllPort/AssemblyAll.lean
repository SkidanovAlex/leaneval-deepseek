import ChallengeDeps
import Submission.Work.BoseBogFSAllPort.RowsAll

/-!
# `Submission.Work.BoseBogFSAllPort.AssemblyAll` — FS `eq:Combined1` at the `All` view

`Work.BoseBoxFock.BogOpBoundFSAll` from the three `N`-free analytic rows

* the zero-point row (`hZP`, produced by `Work.BoseBogFS.hZP_of_lattice` from
  `Work.BoseBogFS.ZPLatticeRow`),
* the denominator row (`hden`, produced by `Work.BoseBogFS.honest_denRow_view`),
* the `𝒞`-form bound (`hlin`, produced by `Work.BoseBogFS.honest_linHi`),

plus the bookkeeping rows of the honest family (χ̂-normalisation, mass row) and the regime
rows.  The reserve is `qw_dNumOpR_le_lin` (the exact shift identity) — **no** `hwinG`/`hwinGS`,
`winKbar`, `Dsup` or `G` occurs.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFSAllPort

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The pins of the `All` view, uniformly in the datum -/

/-- The conjuncts of `RViewFSAll` that the assembly reads, for an arbitrary family `D`. -/
theorem viewFSAll_pins_gen {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {D : Work.BoseFixR.KzDatum} (hview : D.viewFSAll v h μ) :
    Nonempty (Work.BoseB7.FSParamsView D.E)
      ∧ D.E.mu = μ
      ∧ D.E.aScat = _root_.BoseGases.a v
      ∧ D.E.ell = ell v μ
      ∧ D.gHat0 = 8 * π * _root_.BoseGases.a v
      ∧ tauSmPin D.F D.E
      ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ D.E.b
          ∧ ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ →
              Work.BoseBoxFock.Q3KernelFSAll K₀ D.F D.T (Work.BoseFixR.KzEnvAt D.E ρ)) := by
  have hv := hview
  unfold Work.BoseFixR.KzDatum.viewFSAll Work.BoseBoxFock.RViewFSAll at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hv
  refine ⟨h1, h2, h3, h4, h11, ?_, h23⟩
  exact tauSmPin_of_tauPin (F := D.F) (E := D.E)
    (eTp := (paramsAt μ (_root_.BoseGases.a v)).eT) (sp := (paramsAt μ (_root_.BoseGases.a v)).s)
    (dp := (paramsAt μ (_root_.BoseGases.a v)).d) (ℓp := ell v μ) h12 h7 h8 h9 h4

/-! ## 2. The capstone -/

/-- `Work.BoseBoxFock.BogOpBoundFSAll` written in this chapter's vocabulary: the frozen
statement with the chapter's copies `Work.BoseBogFS.KzBogFS` / `Work.BoseBogFS.RHi` (the
chapter's copies are definitionally equal to the frozen ones), so that `bogOpBound_at`'s
conclusion matches it syntactically. -/
def BogOpBoundFSAllB (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (D : ℝ → Work.BoseFixR.KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (Work.BoseFixR.KzEnvAt (D μ).E ρ)
                (RHi (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0) * (D μ).F.normSq f

/-- The conversion to the frozen statement (definitional). -/
theorem bogOpBoundFSAll_of_B {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    {D : ℝ → Work.BoseFixR.KzDatum} (hb : BogOpBoundFSAllB v h R D) :
    Work.BoseBoxFock.BogOpBoundFSAll v h R D := hb

/-- The frozen-`RHi` form of the index-set bridge (the two `RHi`s are definitionally equal). -/
theorem filter_RHi_FS_eq (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (h0 : ¬ Work.BoseBoxFock.RHi F E 0) :
    Finset.univ.filter (Work.BoseBoxFock.RHi F E)
      = (Work.BoseB7.excited Mode).filter (Work.BoseBoxFock.RHi F E) :=
  filter_RHi_eq F E h0

/-- **FS `eq:Combined1` at the `All` view**, from the three `N`-free analytic rows. -/
theorem bogOpBoundFSAll_of_analytic {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {R r₁ C : ℝ} (D : ℝ → Work.BoseFixR.KzDatum)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (εr : ℝ) (hεr : 0 < εr)
    (hRℓ : ∀ μ : ℝ, Adm v εr μ → R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hreg : ∀ μ : ℝ, Adm v εr μ → R / ell v μ ≤ r₁)
    (hcond : ∀ μ : ℝ, Adm v εr μ → C * (R / ell v μ) ^ 2 ≤ 1 / 4)
    (hδD1 : ∀ μ : ℝ, Adm v εr μ → honestDD v μ R ≤ 1 / 2)
    (εz C₄ : ℝ) (hεz : 0 < εz) (hC₄ : 0 ≤ C₄)
    (hZP : ∀ μ : ℝ, Adm v εz μ → (D μ).viewFSAll v h μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          (bogA (D μ).E ρ k) (bogB (D μ).E ρ k))
        ≤ -(4 * π * lhyC * ρ ^ 2 * (_root_.BoseGases.a v) * ell3 v μ
              * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0
          + C₄ * errBracket v R μ)
    (εd : ℝ) (hεd : 0 < εd)
    (hden : ∀ μ : ℝ, Adm v εd μ → (D μ).viewFSAll v h μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ k : (D μ).Mode,
        2 * ρ * ((D μ).E.W1 0) * (1 - honestDD v μ R)
          ≤ (D μ).E.tau k + 2 * ρ * ((D μ).E.W1 k))
    (εl Cl : ℝ) (hεl : 0 < εl) (hCl : 0 ≤ Cl)
    (hlin : ∀ μ : ℝ, Adm v εl μ → (D μ).viewFSAll v h μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ f : (D μ).F.H,
        (D μ).T.NWindow (D μ).E.bigM f →
        |(D μ).F.qw f
          (∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi (D μ).F
              (Work.BoseFixR.KzEnvAt (D μ).E ρ)),
            ((1 / 2 : ℝ) * bogC (D μ).E ρ k) •
              ((D μ).F.a k + (D μ).F.aDag k + (D μ).F.a (-k) + (D μ).F.aDag (-k)))|
          ≤ Cl * errBracket v R μ * (D μ).F.normSq f)
    (hchi : ∀ μ : ℝ, Adm v εd μ → (D μ).viewFSAll v h μ →
      (∑ k : (D μ).Mode, ((D μ).E.hatChi k) ^ 2) ≤ 1)
    (hW0pos : ∀ μ : ℝ, Adm v εd μ → (D μ).viewFSAll v h μ → 0 < (D μ).E.W1 0)
    (hW0up : ∀ μ : ℝ, Adm v εd μ → (D μ).viewFSAll v h μ →
      (D μ).E.W1 0 ≤ 8 * π * (_root_.BoseGases.a v) * (1 + honestDW v μ R C)) :
    BogOpBoundFSAllB v h R D := by
  set ε₀ : ℝ := min (min (min (min εr εd) εz) εl) (1 / 2) with hε₀def
  set Capp : ℝ := C₄ + Cl + 4 * (2 * C + 8192) / ((2 : ℝ) ^ 26 * π) + 1 with hCappdef
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (lt_min (lt_min (lt_min hεr hεd) hεz) hεl) (by norm_num)
  have hCapp0 : 0 ≤ Capp := by
    rw [hCappdef]
    have h1 : 0 ≤ 4 * (2 * C + 8192) / ((2 : ℝ) ^ 26 * π) := by
      apply div_nonneg _ (by positivity)
      linarith
    linarith
  have hε₀1 : ε₀ ≤ 1 := by
    rw [hε₀def]; exact le_trans (min_le_right _ _) (by norm_num)
  have hlt_er : ε₀ ≤ εr := by
    rw [hε₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hlt_ed : ε₀ ≤ εd := by
    rw [hε₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hlt_ez : ε₀ ≤ εz := by
    rw [hε₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlt_el : ε₀ ≤ εl := by
    rw [hε₀def]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨ε₀, Capp, hε₀pos, hCapp0, ?_⟩
  intro μ hadm hview ρ hρ0 hclose f hf
  have hμ : 0 < μ := hadm.1
  have hdil1 : Work.BoseFixR.dil v μ ≤ 1 := le_trans hadm.2.1 hε₀1
  have hAdr : Adm v εr μ := Work.BoseBogFS.adm_mono hlt_er hadm
  have hAdd : Adm v εd μ := Work.BoseBogFS.adm_mono hlt_ed hadm
  have hAdz : Adm v εz μ := Work.BoseBogFS.adm_mono hlt_ez hadm
  have hAdl : Adm v εl μ := Work.BoseBogFS.adm_mono hlt_el hadm
  -- the view pins
  obtain ⟨hPne, hmuE, hacE, hellE, hg0E, hpin, hgate⟩ := viewFSAll_pins_gen (D := D μ) hview
  obtain ⟨hP⟩ := hPne
  have hs : 0 < (D μ).E.s := by rw [hP.s_eq]; exact Work.BoseBox.fsXp_pos hP.t_pos
  have hd : 0 < (D μ).E.d := by rw [hP.d_eq]; exact Work.BoseBox.fsXp_pos hP.t_pos
  have heT0 : 0 < (D μ).E.eT := by rw [hP.eT_eq]; exact Work.BoseBox.fsXp_pos hP.t_pos
  have heT1 : (D μ).E.eT ≤ 1 := by
    rw [hP.eT_eq]
    exact Work.BoseBox.fsXp_le_one hP.t_pos hP.t_le_one (by norm_num)
  have hℓ : 0 < (D μ).E.ell := Work.BoseB7.ell_pos (D μ).E hP
  have hκpos : 0 < (D μ).E.KL * Real.sqrt ((D μ).E.mu * (D μ).E.aScat) := by
    have h1 : 0 < (D μ).E.KL := lt_of_lt_of_le zero_lt_one hP.one_le_KL
    have h2 : 0 < (D μ).E.mu * (D μ).E.aScat := by
      rw [hmuE, hacE]; exact mul_pos hμ hav
    exact mul_pos h1 (Real.sqrt_pos.mpr h2)
  have hρpos : 0 < ρ := rho_pos_of_close v hε₀1 hav hadm hclose
  -- the gate at `ρ`
  obtain ⟨K₀, b₀, hK₀, hb₀, hb₀b, hgateρ⟩ := hgate
  have hgρ : Work.BoseBoxFock.Q3KernelFSAll K₀ (D μ).F (D μ).T
      (Work.BoseFixR.KzEnvAt (D μ).E ρ) := hgateρ ρ hclose
  -- the numerator
  have hnum : BogNumeric (D μ).F (D μ).E ρ :=
    bogNumeric_of_denRow (D μ).F (D μ).T (D μ).E ρ (honestDD v μ R) hgρ hpin
      heT0.le heT1 hs.le hd.le hℓ.le hρpos (hW0pos μ hAdd hview)
      (by have h := hδD1 μ hAdr; linarith) (hden μ hAdd hview ρ hclose)
  -- the `𝒞`-slot
  have hKAP := hKAP_of_rowsAll R D ε₀ (fun μ => honestDW v μ R C) (fun μ => honestDD v μ R)
    (fun μ ρ => honestDelta v μ R C ρ) hε₀1 hav
    (fun μ _ => by rw [honestDW]; positivity)
    (fun μ hadm' => by
      rw [honestDW_eq]
      have h := hcond μ (Work.BoseBogFS.adm_mono hlt_er hadm')
      rw [ell_eq] at h
      linarith)
    (fun μ _ => by rw [honestDD]; positivity)
    (fun μ hadm' => hδD1 μ (Work.BoseBogFS.adm_mono hlt_er hadm'))
    (fun μ hadm' hview' => hchi μ (Work.BoseBogFS.adm_mono hlt_ed hadm') hview')
    (fun μ hadm' hview' => hW0pos μ (Work.BoseBogFS.adm_mono hlt_ed hadm') hview')
    (fun μ hadm' hview' => hW0up μ (Work.BoseBogFS.adm_mono hlt_ed hadm') hview')
    (fun μ hadm' hview' ρ' hclose' =>
      hden μ (Work.BoseBogFS.adm_mono hlt_ed hadm') hview' ρ' hclose')
    (fun μ' _ hview' => (viewFSAll_pins_gen (D := D μ') hview').2.2.2.2.1)
    (fun μ' _ hview' => (viewFSAll_pins_gen (D := D μ') hview').2.1)
    (fun μ' _ hview' => (viewFSAll_pins_gen (D := D μ') hview').2.2.2.1)
    (fun μ' _ hview' => (viewFSAll_pins_gen (D := D μ') hview').2.2.1)
    (fun μ ρ _ => rfl)
  -- the reserve
  have hlinf : ∀ g : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM g →
      |(D μ).F.qw g (bogCform (D μ).F (D μ).E ρ
        ((Work.BoseB7.excited (D μ).Mode).filter
          (Work.BoseBoxFock.RHi (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ))))|
        ≤ (Cl * errBracket v R μ) * (D μ).F.normSq g := by
    intro g hg
    have hrow := hlin μ hAdl hview ρ hclose g hg
    have hfe : (Work.BoseB7.excited (D μ).Mode).filter
          (Work.BoseBoxFock.RHi (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ))
        = Finset.univ.filter
          (Work.BoseBoxFock.RHi (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ)) :=
      (filter_RHi_FS_eq (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ)
        (not_RHi_zero (D μ).F (Work.BoseFixR.KzEnvAt (D μ).E ρ) hκpos)).symm
    simpa only [bogCform, bogV, Work.BoseBoxFock.RHi, Work.BoseBogFS.RHi, hfe] using hrow
  have hres := qw_dNumOpR_le_lin (D μ).F (D μ).T (D μ).E ρ (Cl * errBracket v R μ) hnum hlinf
  -- the §11 arithmetic
  have hδrow : honestDelta v μ R C ρ
      ≤ 4 * (2 * C + 8192) * Work.BoseFixR.dil v μ * (R / (_root_.BoseGases.a v)) ^ 2 :=
    honestDelta_le hav hμ.le hC hR.le (one_le_Kl_of_adm hε₀1 hav hadm)
  have hδnn : 0 ≤ honestDelta v μ R C ρ :=
    honestDelta_nonneg (v := v) (R := R) (C := C) (μ := μ) (ρ := ρ) hC hav.le
  have harith := hArith_of_pieces v R μ ρ (honestDelta v μ R C ρ)
    (C₄ * errBracket v R μ) (Cl * errBracket v R μ) C₄ Cl (4 * (2 * C + 8192))
    (D μ).gHat0 hav hμ hdil1 hg0E hclose hδrow (by positivity) le_rfl le_rfl hC₄ hCl
  -- FS `eq:Combined1`
  have hmain := bogOpBound_at v h R (D μ) μ ρ hnum hmuE hellE
    (C₄ * errBracket v R μ) (Cl * errBracket v R μ) (honestDelta v μ R C ρ) Capp
    hδnn (hZP μ hAdz hview ρ hclose) (hKAP μ hadm hview ρ hclose) hres harith f hf
  simpa only [hCappdef, errBracket, ell3, hellE, mul_assoc] using hmain

end Work.BoseBogFSAllPort
