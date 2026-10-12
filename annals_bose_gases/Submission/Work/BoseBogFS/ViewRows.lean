import ChallengeDeps
import Submission.Work.BoseBogFS.NumericView
import Submission.Work.BoseBogFS.ViewBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ViewRows` — the rows of the capstone that come from the view

The capstone `Work.BoseBogFS.bogOpBoundAtFS_of_sharpMatchL` (`SharpL.lean`) takes the view
`(hview : (D μ).viewFS v h μ)`, which is node `D-FS`'s canonical
`Submission.Work.BoseBoxFock.RViewFS`.  Three of its rows are *pure projections* of that view
(`hmu`, `hell`, `hascat`, and the datum's `ĝ(0)`), two more are the Bessel bundle
(`Cn` with `Cn ≤ 16` and the `n₊^χ ≤ Cn·n₊` inequality), one is the positivity of the matrix
window `𝓜`, and one (`hnum`) is this chapter's `BogNumeric` — a *theorem* about the view
(`bogNumeric_of_viewFS`), composed here with the canonical-to-chapter bridge
`RViewFS_of_canonical`.

This module exposes all of those at the **canonical** view (the one the capstone and the
`D-FS` node use), so that a consumer writing

```
bogOpBoundAtFS_of_sharpMatchL v h R D ε₀ hε₀1 M η Cβ … (fun μ hadm hview => …) …
```

can fill the view-shaped rows with `Work.BoseBogFS.canView_mu hview` (etc.) instead of
destructuring the 23-fold conjunction by hand.

Also here: `bogD_le_self` / `bogD_le_bogA` — the diagonal coefficient `𝒟_k = ½(𝒜_k+√(𝒜_k²−ℬ_k²))`
never exceeds `𝒜_k`, so the capstone's row `hDsup : ∀ k, 𝒟_k ≤ Dsup μ ρ` follows from the
coefficient row `hAwin` together with the *scalar* row `A μ ρ ≤ Dsup μ ρ`.  (The honest datum
therefore has one fewer row to prove: it may take `Dsup μ ρ := A μ ρ` if that is large enough
for `hKbig`, and `Dsup μ ρ` larger otherwise, with `A μ ρ ≤ Dsup μ ρ` in either case.)
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. `𝒟 ≤ 𝒜` -/

/-- `½(𝒜 + √(𝒜²−ℬ²)) ≤ 𝒜` whenever `𝒜 ≥ 0` and `|ℬ| ≤ 𝒜` (`√(𝒜²−ℬ²) ≤ 𝒜`). -/
theorem bogD_le_self {A B : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A) :
    Submission.BoseGases.bogD A B ≤ A := by
  rw [Submission.BoseGases.bogD]
  linarith [Submission.BoseGases.bogS_sq_le hA hB]

/-- The chapter's `𝒟`-field at the datum. -/
theorem bogD_le_bogA (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k) : bogD E ρ k ≤ bogA E ρ k :=
  bogD_le_self hA.le hB

/-- **`hDsup` from the coefficient row.**  If `𝒜_k ≤ A` and `A ≤ Dsup`, then `𝒟_k ≤ Dsup`. -/
theorem hDsup_of_numeric_le {F : FockData Mode} {E : Q3Env Mode} {ρ A Dsup : ℝ}
    (hnum : BogNumeric F E ρ) (hA : ∀ k : Mode, bogA E ρ k ≤ A) (hAD : A ≤ Dsup) :
    ∀ k : Mode, bogD E ρ k ≤ Dsup :=
  fun k => le_trans (bogD_le_bogA E ρ k (hnum.hA k) (hnum.hB k)) (le_trans (hA k) hAD)

/-! ## 2. The projections of the canonical view -/

variable {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {F : FockData Mode}
variable {T : Work.BoseB7A.TildeData F} {E : Q3Env Mode} {gHat0 : ℝ}

/-- The canonical view's `μ`-row. -/
theorem canView_mu (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) : E.mu = μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h2

/-- The canonical view's `a_scat`-row. -/
theorem canView_aScat (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) : E.aScat = a v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h3

/-- The canonical view's `ℓ`-row. -/
theorem canView_ell (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) : E.ell = ell v μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h4

/-- The canonical view's `ĝ(0)`-row. -/
theorem canView_gHat0 (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) :
    gHat0 = 8 * π * a v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h11

/-- The canonical view's `𝓜`-row. -/
theorem canView_bigM (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) :
    E.bigM = bigM (paramsAt μ (a v)) (a v) μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h5

/-- **The matrix window is nonnegative** at the canonical view (`0 < μ`, `0 < a v`). -/
theorem canView_bigM_nonneg (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0)
    (hμ : 0 < μ) (hav : 0 < a v) : 0 ≤ E.bigM := by
  rw [canView_bigM hview]
  exact (Work.BoseBox.bigM_pos_of_params hμ hav).le

/-- **The Bessel bundle of the canonical view**: `∃ Cn, 0 ≤ Cn ∧ Cn ≤ 16 ∧ n₊^χ ≤ Cn·n₊`. -/
theorem canView_bessel (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧
      ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h22

/-! ## 3. `BogNumeric` at the canonical view -/

/-- **`BogNumeric` at the canonical view** — the composition of the bridge
`RViewFS_of_canonical` with the chapter's `bogNumeric_of_viewFS`.  This discharges the
capstone's `hnum` row from the canonical `viewFS` plus the honest `Ŵ₁` data. -/
theorem bogNumeric_of_viewFS_canonical (hview : Work.BoseBoxFock.RViewFS v h μ F T E gHat0)
    (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    {ρ : ℝ} (hclose : CloseCondFS v μ ρ) (hρ : 0 < ρ)
    {w₀ : ℝ} (hw₀ : 0 < w₀) (hε1 : E.eT < 1)
    (hκ : 0 < E.KL * Real.sqrt (E.mu * E.aScat))
    (hc₁ : (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * (16 * π * a v) / (1 - E.eT))
      ≤ 4 * (E.KL * Real.sqrt (E.mu * E.aScat)))
    (hball : ∀ k : EuclideanSpace ℝ (Fin 3),
      ‖k‖ ≤ (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * (16 * π * a v) / (1 - E.eT)) →
        w₀ ≤ chat (W1fun v h (ell v μ)) k) :
    BogNumeric F E ρ :=
  bogNumeric_of_viewFS (RViewFS_of_canonical hview) hv hvrad hR hv_supp hRℓ hclose hρ hw₀ hε1
    hκ hc₁ hball

end Work.BoseBogFS
