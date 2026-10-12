import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.Numeric
import Submission.Work.BoseBogFS.tauSm_ge_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.NumericPin` — the positivity rows from the `τ̃`-pin alone

`Numeric.lean` reduces the two positivity rows of `BogNumeric` to

* the quantitative high-band bound `(1−ε_T)(‖k‖−(sℓ)⁻¹)² ≤ τ̃(k)` (there supplied as
  `hge`), and
* the two `Ŵ₁` inputs `−w₁ ≤ Ŵ₁` (everywhere), `w₀ ≤ Ŵ₁` (below `c₁`).

Here the first is *discharged*: `tauSm_ge_sq` derives it from the `τ̃`-pin `tauSmPin`
(`RViewFS`'s conjunct 12), so the only remaining inputs are the two `Ŵ₁` rows — supplied at
the honest datum by `abs_W1_le_viewFS` (`w₁ = 16πa`) and by `W1_lowband_viewFS`
(the small-ball positivity of `Ŵ₁`, FS's `Ŵ₁ ≥ w₀ > 0` near the origin).

The threshold is the explicit `c₁ = (sℓ)⁻¹ + √(2ρw₁/(1−ε_T))`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The two positivity rows, from the `τ̃`-pin.**  With `ρ > 0`, `w₀ > 0`, `w₁ ≥ 0`,
`0 ≤ ε_T < 1` and the two `Ŵ₁` rows, both `𝒜 = τ̃ + ρŴ₁` and `𝒜 + ℬ = τ̃ + 2ρŴ₁` are
strictly positive. -/
theorem bogA_pos_of_pin (F : FockData Mode) (E : Q3Env Mode) (ρ w₀ w₁ : ℝ)
    (hpin : tauSmPin F E) (hε0 : 0 ≤ E.eT) (hε1 : E.eT < 1)
    (hs : 0 < E.s) (hd : 0 ≤ E.d) (hℓ : 0 < E.ell)
    (hρ : 0 < ρ) (hw₀ : 0 < w₀) (hw₁ : 0 ≤ w₁)
    (hWlo : ∀ k : Mode, -w₁ ≤ E.W1 k)
    (hW : ∀ k : Mode,
      ‖F.kmom k‖ ≤ (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT)) → w₀ ≤ E.W1 k) :
    (∀ k : Mode, 0 < bogA E ρ k) ∧ (∀ k : Mode, 0 < bogA E ρ k + bogB E ρ k) :=
  bogA_pos_of_honest F E ρ ((E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT))) w₀ w₁
    hε1 hρ hw₀ hw₁ (fun k => tauSm_nonneg F E hpin hε0 hε1.le hs.le hd hℓ.le k)
    (fun k hk => tauSm_ge_sq F E hpin hε0 hε1.le hs hℓ k hk) rfl hWlo hW

/-- **`BogNumeric` from the gate and the two `Ŵ₁` rows.**  This is
`bogNumeric_of_honest` with the `τ̃`-inputs (nonnegativity and the high-band bound)
discharged by `tauSmPin`. -/
theorem bogNumeric_of_pin (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Q3Env Mode) (ρ w₀ w₁ K₀ : ℝ)
    (hgate : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ))
    (hpin : tauSmPin F E) (hε0 : 0 ≤ E.eT) (hε1 : E.eT < 1)
    (hs : 0 < E.s) (hd : 0 ≤ E.d) (hℓ : 0 < E.ell)
    (hρ : 0 < ρ) (hw₀ : 0 < w₀) (hw₁ : 0 ≤ w₁)
    (hWlo : ∀ k : Mode, -w₁ ≤ E.W1 k)
    (hW : ∀ k : Mode,
      ‖F.kmom k‖ ≤ (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * w₁ / (1 - E.eT)) → w₀ ≤ E.W1 k) :
    BogNumeric F E ρ :=
  BogNumeric.of_gate F T E ρ hgate
    (bogA_pos_of_pin F E ρ w₀ w₁ hpin hε0 hε1 hs hd hℓ hρ hw₀ hw₁ hWlo hW).1
    (bogA_pos_of_pin F E ρ w₀ w₁ hpin hε0 hε1 hs hd hℓ hρ hw₀ hw₁ hWlo hW).2

end Work.BoseBogFS
