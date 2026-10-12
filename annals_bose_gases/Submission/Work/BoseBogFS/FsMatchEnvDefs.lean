import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBogFS.hZP_of_match
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.FsMatchEnvDefs` — the **envelope** identification

`FINDING_honest_interface.md` §3.2 records the obstruction that blocks `FsMatch*` at the honest
family: the row `hB : bogB E ρ k = ρ_z a·β(‖modePos n (e k)‖)` is an *equality through a function
of the mesh norm*, so it forces the honest kernel `E.W1` to be radial in the mode label — which
this corpus cannot prove (`IsRadial χ` is not derivable: Mathlib's `ContDiffBump.toFun` is
`Classical.choice`-based and exposes only evenness).

This module records the **repair**: replace the equality rows by the *inequality* rows that the
honest data can prove — in particular

```
hB : ∀ k, bogB E ρ k ≤ ρ_z a·β(‖modePos n (e k)‖)
```

(an "envelope" row: provable from the *proved* Lipschitz bound
`Work.BoseGateFS.fderiv_chat_W1fun_le`, `‖∇Ŵ₁‖ ≤ 16πR·a v`, together with `Ŵ₁(0) = ∫W₁` and the
choice `β(r) = 8π + ηr`), and keep `hA` as the inequality of `FsMatchLe`/`FsMatchInj`.  The
transfer then costs one extra explicit *excess* per mode and **no radiality at all**.

Why the transfer still works: with `A₁ := bogA`, `A₂ := fsA`, `B₁ := bogB`, `B₂ := fsB`,
`𝒵(A,B) = A − √(A²−B²)` is *decreasing* in `A` and *increasing* in `B`; so for
`A₁ ≤ A₂`, `B₁ ≤ B₂` and the pairing row `B₂ ≤ A₁`,

```
𝒵(A₁,B₁) ≤ 𝒵(A₁,B₂) = 𝒵(A₂,B₂) + (𝒵(A₁,B₂) − 𝒵(A₂,B₂))
                     ≤ 𝒵(A₂,B₂) + 2·B₂·(A₂−A₁)/((A₁−B₂)+(A₂−B₂))
```

(the last step is `Work.BoseBogFS.bogZeroPoint_sub_le`).  Summing over the image of the injection
and using the nonnegativity of the model summands (`FsMatchInj.subsum`) gives the transfer with
the explicit excess `EnvExcess`.

The `𝒞`-row is the same shape: `bogKappaErr A B κ = 2κ²/(A+B)` is *decreasing* in `A+B` and even
in `κ`, so `|bogC| ≤ |fsC|` (row `hC`) plus the *reverse* rows `fsA+fsB ≤ bogA+bogB`
(`hABlow`) give the model's `𝒞`-bound plus the explicit excess `KapEnvExcess`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The envelope identification**: `FsMatchInj` with the kernel rows relaxed from equalities to
the inequalities the honest data can prove. -/
structure FsMatchEnv (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) where
  n : ℕ
  D : FsBogData n
  e : Mode → modeIdx n
  hinj : Function.Injective e
  hρ : D.ρz = ρ
  ha : D.a = E.aScat
  hℓ : D.ℓ = E.ell
  hz : D.z = bogZ E ρ
  hμ : D.μ = E.mu
  /-- the diagonal kernel: the datum's `𝒜` is *below* the model's. -/
  hA : ∀ k : Mode, bogA E ρ k ≤ fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n (e k))
  /-- the off-diagonal kernel: the datum's `ℬ` is *below* the model's (the envelope row). -/
  hB : ∀ k : Mode, bogB E ρ k ≤ fsB D.ρz D.a D.K (modePos n (e k))
  /-- the **pairing row**: the model's `ℬ` still sits below the datum's `𝒜` (so that the excess
  formula's denominator is positive). -/
  hpair : ∀ k : Mode, fsB D.ρz D.a D.K (modePos n (e k)) ≤ bogA E ρ k
  /-- the mass row, in the direction the transfer consumes (the model's `fsGω0` may replace the
  datum's `Ŵ₁ω(0)` only up to an excess — see the assembly). -/
  hGw : fsGω0 D.ρz D.a D.K ≤ E.W1omega0
  /-- the `κ`-coefficient row. -/
  hG0 : fsG0 D.ρz D.a D.ℓ D.z D.chiM ≤ gHat0
/-- The zero-point excess of the envelope transfer: one explicit summand per box mode, with the
two slacks separated (the `A`-slack via `bogZeroPoint_sub_le`, the `B`-slack via the `B`-Lipschitz
bound `𝒵(A,B₂) − 𝒵(A,B₁) ≤ (B₂−B₁)·B₂/(A−B₂)`). -/
def EnvExcess (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ)
    (M : FsMatchEnv F E ρ gHat0) : ℝ :=
  ∑ k : Mode,
    (2 * fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k))
        * (fsA M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2 (modePos M.n (M.e k)) - bogA E ρ k)
        / ((bogA E ρ k - fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k)))
            + (fsA M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2 (modePos M.n (M.e k))
                - fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k))))
      + fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k))
          * (fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k)) - bogB E ρ k)
          / (bogA E ρ k - fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k))))

/-- The `κ`-excess of the envelope transfer: one explicit summand per box mode. -/
def KapEnvExcess (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ)
    (M : FsMatchEnv F E ρ gHat0) : ℝ :=
  ∑ k : Mode, 2 * (fsC M.D.ℓ M.D.ρz M.D.μ M.D.a M.D.z M.D.χh (modePos M.n (M.e k))) ^ 2
        / (fsA M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2 (modePos M.n (M.e k))
            + fsB M.D.ρz M.D.a M.D.K (modePos M.n (M.e k)))

/-! ## The sharp comparison at the envelope datum

`SharpCmpWithInj` (`FsMatchInjSharp.lean`) is stated at an `FsMatchInj`; its *body* mentions only
`M.n` and `M.D`.  The envelope route needs the same proposition at an `FsMatchEnv` datum, so we
repeat the `abbrev` with the other structure.  Every producer of `SharpCmpWithInj` (in
particular `sharpCmpWith_L_inj`, `sharpCmpWith_L_of_rows_inj` from `FsMatchInjSharp.lean` /
`SharpL.lean`, and `fsZeroPoint_le_sharpL` itself) produces this one on the same data. -/

/-- **The sharpened lattice comparison at the envelope datum**: the mesh display
`fsZeroPoint_le_sharpL`'s conclusion, with the budget `Er` left free. -/
abbrev SharpCmpWithEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) (M : FsMatchEnv F E ρ gHat0)
    (Er : ℝ) : Prop :=
  zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2
    ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
        * ((Work.BoseB6.meshD M.n) ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
      + fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
      + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
          * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3
      + ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
          * Er

end Work.BoseBogFS
