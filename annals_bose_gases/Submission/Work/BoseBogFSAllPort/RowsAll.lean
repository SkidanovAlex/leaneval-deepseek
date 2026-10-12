import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFSAllPort.ReserveAll
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFSAllPort.RowsAll` — the row producers at the `All` view

Everything the `All` capstone `Work.BoseBoxFock.BogOpBoundFSAll` needs, produced from the
frozen `All` view `Work.BoseBoxFock.RViewFSAll`:

* the `§10`-gate lemmas (`BogNumeric`'s evenness/adjointness rows) at `Q3KernelFSAll`;
* `BogNumeric` itself, from the `All` gate plus the two positivity rows — and those from the
  honest denominator row and the mass row (no `τ̃`-threshold/cut-off radius is used);
* the `𝒞`-slot `hKAP`, the `viewFSAll` copy of `Work.BoseBogFS.hKAP_of_rows`;
* the pins (conjuncts 1–12 and 23) read off the `All` view, including `tauSmPin`
  (`Work.BoseBogFS.tauSmPin_of_tauPin`) and the gate.

These are mechanical ports: `Work.BoseBoxFock.RViewFSAll` has the conjunct list of
`RViewFS` in the *same order*, with the last conjunct at `Q3KernelFSAll`, and `Q3KernelFSAll`
has the field names of `Q3KernelFS`.
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

/-! ## 1. The `§10` gate at `Q3KernelFSAll` -/

theorem ccrK_self_le_oneAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T E) (k : Mode) : F.ccrK k k ≤ 1 := by
  have hh := h.hasKernel_noWrap k k (noWrap_self F k)
  rw [sub_self] at hh
  have h1 : E.hatChiSq 0 ≤ 1 := (abs_le.mp (h.hatChiSq_le 0)).2
  have h2 : 0 ≤ E.hatChi k * E.hatChi k := mul_self_nonneg _
  linarith

theorem bogCcr2_le_twoAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T E) (k : Mode) : bogCcr2 F k ≤ 2 := by
  have h1 := ccrK_self_le_oneAll F T E h k
  have h2 := ccrK_self_le_oneAll F T E h (-k)
  simp only [bogCcr2]
  linarith

theorem bogA_even_of_gateAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogA E ρ (-k) = bogA E ρ k := by
  have hh := h.A_even k
  simpa only [bogA, Work.BoseFixR.KzEnvAt] using hh

theorem bogB_even_of_gateAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogB E ρ (-k) = bogB E ρ k := by
  have hh := h.B_even k
  simpa only [bogB, Work.BoseFixR.KzEnvAt] using hh

theorem bogC_even_of_gateAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogC E ρ (-k) = bogC E ρ k := by
  have hh := h.hatChi_even
  simp only [Work.BoseFixR.KzEnvAt] at hh
  simp only [bogC, hh]

theorem bogAB_of_gateAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    |bogB E ρ k| ≤ bogA E ρ k := by
  have hh := h.AB k
  simpa only [bogA, bogB, Work.BoseFixR.KzEnvAt] using hh

/-- **`BogNumeric` from the `All` gate.**  The `All` twin of `Work.BoseBogFS.BogNumeric.of_gate`. -/
theorem bogNumeric_of_gateAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ))
    (hA : ∀ k, 0 < bogA E ρ k) (hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k) :
    BogNumeric F E ρ where
  hA := hA
  hB := fun k => bogAB_of_gateAll F T E ρ h k
  hAB := hAB
  hAe := fun k => (bogA_even_of_gateAll F T E ρ h k).symm
  hBe := fun k => (bogB_even_of_gateAll F T E ρ h k).symm
  hCe := fun k => (bogC_even_of_gateAll F T E ρ h k).symm
  hccr := fun k => bogCcr2_le_twoAll F T (Work.BoseFixR.KzEnvAt E ρ) h k

/-- **`BogNumeric` from the `All` gate, FS's denominator row and the mass row.**  The two
positivity rows `0 < 𝒜`, `0 < 𝒜+ℬ` follow from the denominator row (`𝒜+ℬ ≥ 2ρŴ₁(0)(1−δ_D) > 0`)
and `τ̃ ≥ 0`, so no cut-off radius enters. -/
theorem bogNumeric_of_denRow (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ δD : ℝ) {K₀ : ℝ}
    (h : Work.BoseBoxFock.Q3KernelFSAll K₀ F T (Work.BoseFixR.KzEnvAt E ρ))
    (hpin : tauSmPin F E) (hε0 : 0 ≤ E.eT) (hε1 : E.eT ≤ 1)
    (hs : 0 ≤ E.s) (hd : 0 ≤ E.d) (hℓ : 0 ≤ E.ell)
    (hρ : 0 < ρ) (hW0 : 0 < E.W1 0) (hδD : δD < 1)
    (hden : ∀ k : Mode, 2 * ρ * (E.W1 0) * (1 - δD) ≤ E.tau k + 2 * ρ * E.W1 k) :
    BogNumeric F E ρ := by
  have hAB : ∀ k : Mode, 0 < bogA E ρ k + bogB E ρ k := by
    intro k
    have h0 : 0 < 2 * ρ * (E.W1 0) * (1 - δD) := by
      have h1 : 0 < 1 - δD := by linarith
      have h2 : 0 < 2 * ρ := by linarith
      exact mul_pos (mul_pos h2 hW0) h1
    have h2 : bogA E ρ k + bogB E ρ k = E.tau k + 2 * ρ * E.W1 k := by
      simp only [bogA, bogB]; ring
    rw [h2]
    linarith [hden k]
  have hA : ∀ k : Mode, 0 < bogA E ρ k := by
    intro k
    have hτ := tauSm_nonneg F E hpin hε0 hε1 hs hd hℓ k
    have h1 : bogA E ρ k = (bogA E ρ k + bogB E ρ k) / 2 + E.tau k / 2 := by
      simp only [bogA, bogB]; ring
    rw [h1]
    linarith [hAB k, hτ]
  exact bogNumeric_of_gateAll F T E ρ h hA hAB

/-- **The numerator-free zero cost of `hAB` at the honest datum.**  For the assembly we need
`E.W1 0 > 0` and `honestDD v μ R < 1`; both are supplied by the caller. -/
theorem bogNumeric_of_denRow_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {R μ ρ : ℝ} (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hpin : tauSmPin (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    {K₀ : ℝ}
    (hgate : Work.BoseBoxFock.Q3KernelFSAll K₀
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
      (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
    (hε0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
    (hε1 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT ≤ 1)
    (hs : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s)
    (hd : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.d)
    (hℓ : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)
    (hρ : 0 < ρ) (hW0 : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0)
    (hδD : honestDD v μ R < 1)
    (hden : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0) * (1 - honestDD v μ R)
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k
          + 2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k)) :
    BogNumeric (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ :=
  bogNumeric_of_denRow _ _ _ ρ (honestDD v μ R) hgate hpin hε0 hε1 hs hd hℓ hρ hW0 hδD hden

/-! ## 2. The `𝒞`-slot at the `All` view -/

/-- **The capstone's `hKAP` from the three honest rows, at `viewFSAll`.**  Copy of
`Work.BoseBogFS.hKAP_of_rows` with the view type changed (its body uses the view only
through the rows). -/
theorem hKAP_of_rowsAll {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (R : ℝ) (D : ℝ → Work.BoseFixR.KzDatum) (ε₀ : ℝ) (δ' δD : ℝ → ℝ) (δ : ℝ → ℝ → ℝ)
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v)
    (hδ'0 : ∀ μ : ℝ, Adm v ε₀ μ → 0 ≤ δ' μ)
    (hδ'1 : ∀ μ : ℝ, Adm v ε₀ μ → δ' μ ≤ 1 / 2)
    (hδD0 : ∀ μ : ℝ, Adm v ε₀ μ → 0 ≤ δD μ)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → δD μ ≤ 1 / 2)
    (hchi : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
      (∑ k : (D μ).Mode, ((D μ).E.hatChi k) ^ 2) ≤ 1)
    (hW0pos : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → 0 < (D μ).E.W1 0)
    (hW0up : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ →
      (D μ).E.W1 0 ≤ 8 * π * a v * (1 + δ' μ))
    (hden : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode,
        2 * ρ * ((D μ).E.W1 0) * (1 - δD μ) ≤ (D μ).E.tau k + 2 * ρ * ((D μ).E.W1 k))
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → (D μ).E.aScat = a v)
    (hδdef : ∀ μ ρ : ℝ, Adm v ε₀ μ → δ μ ρ = 4 * (δ' μ + δD μ)) :
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFSAll v h μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
          (bogA (D μ).E ρ k) (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
        ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + δ μ ρ) := by
  intro μ hadm hview ρ hclose
  have hμ : 0 < μ := hadm.1
  have hℓ : 0 ≤ (D μ).E.ell := by
    rw [hell μ hadm hview, ell_eq]
    exact Work.BoseBogFS.sideAt_nonneg μ (a v)
  have hρ : 0 < ρ := rho_pos_of_close v hε₀1 hav hadm hclose
  have hg0' : (D μ).gHat0 = 8 * π * (D μ).E.aScat := by
    rw [hg0 μ hadm hview, hascat μ hadm hview]
  have hW0up' : (D μ).E.W1 0 ≤ 8 * π * (D μ).E.aScat * (1 + δ' μ) := by
    rw [hascat μ hadm hview]
    exact hW0up μ hadm hview
  have hmain := bogKAP_of_rows (D μ).F (D μ).E ρ (D μ).gHat0 (δ' μ) 0 (δD μ) hρ hℓ
    hg0' (hW0pos μ hadm hview) hW0up'
    (hδ'0 μ hadm) (hδ'1 μ hadm) le_rfl (by norm_num) (hδD0 μ hadm) (hδD1 μ hadm)
    (by simpa using hchi μ hadm hview) (hden μ hadm hview ρ hclose)
  have h1 : (1 : ℝ) + 4 * (δ' μ + 0 + δD μ) = 1 + δ μ ρ := by
    rw [hδdef μ ρ hadm]; ring
  have h2 : (ρ - (D μ).E.mu) ^ 2 * ((D μ).gHat0 / 2) * (D μ).E.ell ^ 3
      = (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ := by
    rw [ell3, hmu μ hadm hview, hell μ hadm hview]
  rw [h2] at hmain
  rw [h1] at hmain
  exact hmain

/-! ## 3. The pins of the `All` view -/

/-- The conjuncts of `RViewFSAll` that the honest assembly reads, destructured. -/
theorem viewFSAll_pins {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ : ℝ} (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ) :
    (∃ hP : Work.BoseB7.FSParamsView (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
        True)
      ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.mu = μ
      ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat = _root_.BoseGases.a v
      ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell = ell v μ
      ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 = 8 * π * _root_.BoseGases.a v
      ∧ tauSmPin (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
      ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀
          ∧ b₀ ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.b
          ∧ ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ →
              Work.BoseBoxFock.Q3KernelFSAll K₀
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
                (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
  have hv := hview
  unfold Work.BoseFixR.KzDatum.viewFSAll Work.BoseBoxFock.RViewFSAll at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hv
  refine ⟨⟨h1.some, trivial⟩, h2, h3, h4, h11, ?_, h23⟩
  exact tauSmPin_of_tauPin (F := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F)
    (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (eTp := (paramsAt μ (_root_.BoseGases.a v)).eT) (sp := (paramsAt μ (_root_.BoseGases.a v)).s)
    (dp := (paramsAt μ (_root_.BoseGases.a v)).d) (ℓp := ell v μ) h12 h7 h8 h9 h4

end Work.BoseBogFSAllPort
