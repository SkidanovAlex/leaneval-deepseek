import ChallengeDeps
import Submission.Work.BoseBogFS.NumericPin
import Submission.Work.BoseBogFS.W1_lowband_viewFS
import Submission.Work.BoseBogFS.abs_W1_le_viewFS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.NumericView` — `BogNumeric` at the honest view

This is the composition that removes the `hnum` hypothesis of
`bogOpBoundFS_of_fsData`/`bogOpBoundFS_of_estimates`: at the honest view `RViewFS` the gate
row is `RViewFS.gate_pin`, the `τ̃`-pin is `RViewFS.tau_pin`, and the two `Ŵ₁` inputs come
from the chapter's own lemmas:

* `−w₁ ≤ Ŵ₁` everywhere with `w₁ = 16πa` — `abs_W1_le_viewFS` (FS `eq:WSestimate`);
* `w₀ ≤ Ŵ₁` below the threshold `c₁ = (sℓ)⁻¹ + √(2ρw₁/(1−ε_T))` — `W1_lowband_viewFS`,
  from the honest small-ball positivity `hball` of `Ŵ₁` (FS's `Ŵ₁ > 0` near the origin)
  together with the regime inequality `c₁ ≤ 4K_L√(μa)`;

the FS parameter block (`0 < s`, `0 ≤ d`, `0 < ℓ`, `0 ≤ ε_T`) comes from the view's
`FSParamsView` (`t = μa³ ∈ (0,1]`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `ℓ = K_ℓ(μa)^{-1/2}`)
via `fsXp_pos`, and `BogNumeric` follows from `bogNumeric_of_pin`.

The only non-parameter inputs left are the close condition `CloseCond v μ ρ`, the
smallness of the threshold (`hc₁`) and the small-ball positivity `hball` of `Ŵ₁`.
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

/-- **`BogNumeric` at the honest view.**  Every row of `BogNumeric` at the datum `(E, ρ)`,
from `RViewFS` and the honest `Ŵ₁` data. -/
theorem bogNumeric_of_viewFS {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ}
    {F : FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Q3Env Mode} {gHat0 : ℝ}
    (hview : RViewFS v h μ F T E gHat0)
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
    BogNumeric F E ρ := by
  -- the gate at the datum
  obtain ⟨K₀, b₀, hK₀, hb₀, hb₀b, hgate⟩ := hview.gate_pin
  have hgate' : Q3KernelFS K₀ F T (KzEnvAt E ρ) := hgate ρ hclose
  -- the FS parameter block
  obtain ⟨hv'⟩ := hview.fsparams
  have hs : 0 < E.s := by rw [hv'.s_eq]; exact fsXp_pos hv'.t_pos
  have hd : 0 ≤ E.d := by rw [hv'.d_eq]; exact (fsXp_pos hv'.t_pos).le
  have hε0 : 0 ≤ E.eT := by rw [hv'.eT_eq]; exact (fsXp_pos hv'.t_pos).le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv'
  have hav : 0 < a v := hview.aScat ▸ hv'.a_pos
  -- the two `Ŵ₁` rows
  have hWlo : ∀ k : Mode, -(16 * π * a v) ≤ E.W1 k :=
    fun k => (abs_le.mp (abs_W1_le_viewFS hview hv hvrad hR hv_supp hRℓ k)).1
  have hW : ∀ k : Mode,
      ‖F.kmom k‖ ≤ (E.s * E.ell)⁻¹ + Real.sqrt (2 * ρ * (16 * π * a v) / (1 - E.eT)) →
        w₀ ≤ E.W1 k :=
    fun k hk => W1_lowband_viewFS hview hκ hc₁ hball k hk
  have hw₁ : (0 : ℝ) ≤ 16 * π * a v := by positivity
  exact bogNumeric_of_pin F T E ρ w₀ (16 * π * a v) K₀ hgate' (hview.tau_pin) hε0 hε1
    hs hd hℓ hρ hw₀ hw₁ hWlo hW

end Work.BoseBogFS
