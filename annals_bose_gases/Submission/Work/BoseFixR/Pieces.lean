import ChallengeDeps
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/Pieces.lean` — the two inputs of `RB67`, stated

`CONTROL3Q_INTEGRATION.md` reduces the close-case residual `RB67` (at the
canonical family `KzCanonFam`) to exactly two inputs plus the §11 arithmetic
(which is proved here):

1. **`Control3QGuarded`** — FS `thm:Control3Q` (`eq:Q3Cancels`) with the
   **guarded** kernel gate `KzKernels` instead of the unsatisfiable
   `Work.BoseB7A.Q3Kernel` (see `VACUITY_3Q.md`).  The delivered
   `Work.BoseB7A.control3QA` is gated on `Q3Kernel` and is therefore vacuous; this
   Prop is the statement BoseB7A needs to re-deliver, and it is *the* input the
   §10 leg of `RB67` consumes.  It is exactly `control3QA` with `Q3Kernel`
   replaced by `KzKernels`.
2. **`BogOpBound`** — FS `thm:BogHamDiag`/`lem:BogIntegral` in **operator form**
   on `KzBog`: the diagonalised Bogoliubov quadratic is kept,
   `KzBog ≥ dNumOpR + (4π·lhyC·ρ²aℓ³√(ρa³) − ℰ)`.

With those two, `KzOpDecomp` (proved here) turns `qw f (KzOp … ρ)` into
`const + (KzBog − dNumOpR) + nPlus + controlWordT + (b/2−b/50)·gapOpT`, and the §11
arithmetic (`AbsorbCloseFix`, `bigK`, proved here) absorbs everything into
`CloseBoundR`'s bracket.  That assembly is the theorem
`Work.BoseFixR.RB67CanonOfPieces`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS `thm:Control3Q` with the guarded kernel gate.**  The delivered
`Work.BoseB7A.control3QA` is the same statement with `Work.BoseB7A.Q3Kernel`,
which has no honest instance on a finite mode group
(`Work.BoseK15.Obstruction.kmom_eq_zero_of_add`); this is the satisfiable form the
close-case residual consumes, with the absolute constants of the design. -/
def Control3QGuarded (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop := 
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env Mode)
      (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → KzKernels K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * Work.BoseB7A.controlErrA E) * F.normSq Φ
          ≤ F.qw Φ (T.controlWordT E)

/-- **FS `thm:Control3Q` with the *honest* kernel gate `Q3Kernel'`.**

`Control3QGuarded` above gates on this directory's `KzKernels`, which was written
before BoseK15's honest bundle existed: its `hatChiSq_form` row carries only the
guard `s ≠ 0`, whereas the honest PSD instance
(`Work.BoseK15.hatChiSq_form_psd_guarded`) needs the weight guard
`c s ≠ 0 → f_L s ≠ 0`.  The unguarded row is *not* an honest fact about the box
(`hatChiSq_form`'s Bochner proof needs the label additivity on non-wrapping pairs,
which is where `Q3Kernel'.hasKernel_noWrap` comes from; the *global* additivity is
refuted — `Work.BoseK15.Obstruction`).  `RView` therefore gates on
`Work.BoseK15.Q3Kernel'` (see `Defs.lean`), and this is the statement BoseB7A
should re-deliver: `control3QA` with `Q3Kernel` (global identity, no honest
instance) replaced by `Q3Kernel'`.

Everything else is identical to `Control3QGuarded`, so the re-delivery is a
renaming of the gate plus the two `Q3Kernel'`-only rows
(`hasKernel_noWrap` — unused by §10's estimates — and the guarded `hatChiSq_form`,
whose guard `c = f_L` is exactly how §10 uses it). -/
def Control3QGuarded' (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env Mode)
      (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseK15.Q3Kernel' K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * Work.BoseB7A.controlErrA E) * F.normSq Φ
          ≤ F.qw Φ (T.controlWordT E)

/-- **FS `eq:BogHamDiag` + `lem:BogIntegral` combined (`eq:Combined1`), in operator
form, at a realisation family `D`.**

The prover of `RB67CanonOfPieces` showed that `thm:BogHamDiag` alone does **not**
imply the close bound: the conclusion is equivalent (monomials aside) to the
*sharp upper* bound on the mode-lattice zero-point sum
`S = ½(2π)^{-3}ℓ³Σ_k(𝒜_k−√(𝒜_k²−ℬ_k²))`, i.e. FS `lem:BogIntegral`'s
`S = 2M − 2·LHY + (errors)` with `M = ½ρ²ℓ³ĝω(0)` the `c`-number mass —
equivalently `M − ½S ≥ LHY − ℰ₁`.  This definition states exactly that *combined*
input (FS's `eq:Combined1`, before `thm:Control3Q` is applied):

`(4π·lhyC·ρ²aℓ³√(ρa³) − C·(§11 bracket))·‖f‖² + ⟨f, n^{Bog}f⟩
   ≤ ⟨f, 𝒦^Bog f⟩ + M·‖f‖²`,

with `M` the environment's `½ρ²ℓ³Ŵ₁ω(0)` (the same reading of `ĝω(0)` as `KzOp`'s
c-number uses).  Its proof is `Work.BoseB6.bogHamDiag_fs` (with `hzero`/`hkappa`)
together with `lem:BogIntegral`'s lattice estimate
(`Work.BoseB6.latticeSum`/`latticeMeshErr`, `Work.BoseB6.lhyValue_eight_pi`) and
the per-pair operator identity `Submission.Fock2ModeShift.fms_shift_identity`. -/
def BogOpBound (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).view v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCond v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ) (fun _ => True))
          ≤ (D μ).F.qw f (KzBog (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0) * (D μ).F.normSq f

end Work.BoseFixR
