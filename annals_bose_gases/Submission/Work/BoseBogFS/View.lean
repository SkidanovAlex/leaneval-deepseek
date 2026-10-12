import ChallengeDeps
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.View` — the projections of `RViewFS`

`RViewFS` (the corrected view, verbatim from `BOSE_BOXFOCK_STATEMENTS.lean.txt` §5.3) is a
single `Prop` with 23 conjuncts.  A consumer — the positivity rows of `BogNumeric`, the
Bessel row of the window bound, the `§10` gate at the datum — needs them one at a time, and
the anonymous-conjunction syntax makes that painful (`hview.2.2.2.…`).  This module names
each of them.

The projection names are `RViewFS.mu`, `RViewFS.aScat`, `RViewFS.ell_eq`, … and they are
usable by dot notation (`hview.W1_pin`), the `hview` being the first explicit argument.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {F : Work.BoseB7.FockData Mode}
variable {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode} {gHat0 : ℝ}

/-- The parameter view of the environment. -/
theorem RViewFS.fsparams (hview : RViewFS v h μ F T E gHat0) :
    Nonempty (Work.BoseB7.FSParamsView E) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h1

/-- The environment's chemical potential is the datum's. -/
theorem RViewFS.mu (hview : RViewFS v h μ F T E gHat0) : E.mu = μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h2

/-- The environment's scattering length is `a v`. -/
theorem RViewFS.aScat (hview : RViewFS v h μ F T E gHat0) : E.aScat = a v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h3

/-- The environment's box side is `ell v μ`. -/
theorem RViewFS.ell_eq (hview : RViewFS v h μ F T E gHat0) : E.ell = ell v μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h4

/-- The datum's `ĝ(0)` is `8πa v`. -/
theorem RViewFS.gHat0_eq (hview : RViewFS v h μ F T E gHat0) : gHat0 = 8 * π * a v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h11

/-- The environment's kinetic symbol is the smoothed `τ̃` (`tauSmPin`). -/
theorem RViewFS.tau_pin (hview : RViewFS v h μ F T E gHat0) : tauSmPin F E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h12

/-- The environment's `𝒜`-kernel is `τ + ρŴ₁`. -/
theorem RViewFS.A_pin (hview : RViewFS v h μ F T E gHat0) :
    E.A = (fun k => E.tau k + E.rho * E.W1 k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h13

/-- The environment's `ℬ`-kernel is `ρŴ₁`. -/
theorem RViewFS.B_pin (hview : RViewFS v h μ F T E gHat0) :
    E.B = (fun k => E.rho * E.W1 k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h14

/-- **The `Ŵ₁` pin.**  `E.W1 = ζ_Λ·Ŵ₁` for a `LowCut` `ζ` at some radius
`Λ ≥ 4K_L√(μa)`; in particular `E.W1 = Ŵ₁` on the ball `‖k‖ ≤ 4K_L√(μa)`. -/
theorem RViewFS.W1_pin (hview : RViewFS v h μ F T E gHat0) :
    ∃ (fu : LowCut) (Λ : ℝ), 4 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ Λ ∧
      E.W1 = (fun k => uvCut fu Λ (F.kmom k) * chat (W1fun v h (ell v μ)) (F.kmom k)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h15

/-- The `χ̂`-pin: the normalised `χ̂(kℓ)`. -/
theorem RViewFS.hatChi_pin (hview : RViewFS v h μ F T E gHat0) :
    E.hatChi = (fun k => chat (chiFun (ell v μ)) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h18

/-- The `χ̂²`-pin. -/
theorem RViewFS.hatChiSq_pin (hview : RViewFS v h μ F T E gHat0) :
    E.hatChiSq = (fun k => chat (fun z => chiFun (ell v μ) z ^ 2) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h19

/-- The `n₊^H` pin: the spectral-profile shift is `(1/32)Σ η_H(n_k)`. -/
theorem RViewFS.NH_pin (hview : RViewFS v h μ F T E gHat0) :
    ∃ fu : LowCut, T.NH = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
      etaH fu (E.KL * Real.sqrt (E.mu * E.aScat)) (F.kmom k) • F.nOp k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h21

/-- **The Bessel row**: `⟨n₊^χf, f⟩ ≤ Cn·⟨Nf, f⟩` with `Cn ≤ 16`. -/
theorem RViewFS.bessel_pin (hview : RViewFS v h μ F T E gHat0) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧
      ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h22

/-- **The gate row**: there are `K₀ ≥ 0`, `b₀ > 0`, `b₀ ≤ E.b` with
`Q3KernelFS K₀ F T (KzEnvAt E ρ)` for every `ρ` in FS's close region. -/
theorem RViewFS.gate_pin (hview : RViewFS v h μ F T E gHat0) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b
      ∧ ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFS K₀ F T (KzEnvAt E ρ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h23

/-- The `f_L` pin: `E.fL` is FS's `f_L` at the environment's parameters. -/
theorem RViewFS.fL_pin (hview : RViewFS v h μ F T E gHat0) :
    ∃ fc : LowCut, E.fL = (fun k => fLFS fc E.KL E.mu E.aScat (F.kmom k)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23⟩ := hview
  exact h20

end Work.BoseBogFS
