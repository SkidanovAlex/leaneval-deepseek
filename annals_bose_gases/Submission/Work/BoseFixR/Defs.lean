import ChallengeDeps
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
import Submission.Work.BoseB6.BogHamDiag
import Submission.Work.BoseB7A.Assembly
import Submission.Work.BoseB7A.Est1.Assembly
import Submission.Work.BoseB7A.Est1.OpZ_Atil_sum
import Submission.Work.BoseB7A.Est1.OpZ_cD_bd
import Submission.Work.BoseB7A.Est1.OpZ_kappa
import Submission.Work.BoseB7A.Est1.OpZ_perK
import Submission.Work.BoseB7A.Est1.R1_split
import Submission.Work.BoseB7A.Est1.Wb1_bound
import Submission.Work.BoseB7A.Est1.Wb2_bound
import Submission.Work.BoseB7A.Est1.cost_arith
import Submission.Work.BoseB7A.Est1.estR1_assembly
import Submission.Work.BoseB7A.Est1.estT2sum_comZ
import Submission.Work.BoseB7A.Est1.wta_bound_aux
import Submission.Work.BoseB7A.Q3Kernel_inhabited
import Submission.Work.BoseB7A.estIntegralOneA
import Submission.Work.BoseB7A.estQ3twoThreeA
import Submission.Work.BoseB7A.sum_abs_kA3_le
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.BoseK15.GuardedKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/Defs.lean` — node `D7` (`R`-subproject): the interface

Node `D7` of `BOSE_BOXNODES_LEAD.md` §4 is the proof of
`Work.BoseBoxFix.nodeRestrictedB_holds`, i.e. FS §7–§11 (`thm:LHY-Box` after
`lem:LocMatrices`).  The design (§2.3) decomposes it into four children:

| child | FS | content |
|---|---|---|
| **R-B4box** | §8 `prop:Hamilton2ndQuant`, `lem:Q3-splitting2`, `thm:Kafz` | the bridge from the box word to the second-quantised substituted Hamiltonian `𝒦(z)` |
| **R-B5** | §9 `lem:Roughbounds`, `prop:FarAway` | the substituted energy is high unless `ρ_z ≈ μ` |
| **R-B6/7** | §10 `thm:BogHamDiag`, `thm:Control3Q` | the substituted energy in the regime `ρ_z ≈ μ` |
| **R-B8** | §11 | the parameter assembly |

This module **fixes the interface** the four children share.  It does not prove
any of the four; it defines the objects they talk about and states them, so that
they can be proved in parallel and combined (`Assembly.lean`).

## The bridge, and why it has this shape

FS §8 second-quantises the box Hamiltonian `𝓗_Λ(μ)` on the bosonic Fock space
over `L²(Λ)` and then, in `thm:Kafz`, replaces the condensate operator `a₀` by a
`c`-number `z ∈ ℂ` with `a₀|z⟩ = z|z⟩`.  Writing `ρ := ρ_z = |z|²/ℓ³` for the
*condensate density*, FS obtain

  `⟨Ψ̃, 𝓗_Λ^{2nd}(μ)Ψ̃⟩ ≥ inf_{z} ⟨Φ(z), 𝒦(z)Φ(z)⟩ − Cμa`     (`eq:IntroK(z)`)

and the whole point is that the second infimum runs over the **§6 window**
`Φ = 1_{[0,𝓜]}(n₊)Φ` (`eq:LocalizedAftercNumber`, carried on the box side by
`Work.BoseBoxFix.SpectralNPlusLe`).

The objects of the interface are therefore

* `Work.BoseB7.FockData Mode` — B4's mode-lattice Fock system (the box
  commutation package `[a_k,a_{k'}†] = χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`);
* `Work.BoseB7.Q3Env Mode` — §10's parameter point and mode-indexed kernels;
* `KzOp F E gHat0 ρ` below — FS `eq:Kz`'s operator `𝒦(z)` at condensate density
  `ρ`, written in B7's vocabulary (`τ`, `Ŵ₁`, `𝓜`, `Q₃`, `Q₂^ex`, …);
* `KzVal F E gHat0 ρ` — the *substituted energy*, i.e. the infimum of the
  quadratic form of `KzOp` over the §6 window.

**The four residual `Prop`s of this chapter are stated about these objects**:
`RB4box` produces them (from a low, spectrally restricted symmetric box state
`Work.BoseKinLoc.BoxState`), and `RB5`/`RB67` bound `KzVal`.  The two bounds
`FarBound`/`CloseBoundR` are FS's `prop:FarAway` (with the factor `2` on the LHY
term) and FS's `eq:Combined1`+`eq:Combined2` (with the §11 errors `ℰ₁, ℰ₂`), on
the complementary density regions `FarCond`/`CloseCond` (FS `eq:Close-I` and its
negation `eq:Close`).

## Conventions

* `X n = (ℝ³)^n` with `ℝ³ = EuclideanSpace ℝ (Fin 3)`, as everywhere in the
  corpus; `abox n ℓ` is the centred box and `sideAt μ (a v)` is FS's healing
  length `ℓ = K_ℓ(μa)^{-1/2}`.
* `dil v μ := μ * (a v)^3` is FS's diluteness `t`; `t ≤ 1` throughout
  (`Adm` + the assembly's `ε₀ ≤ 1`).
* **Every error constant is free** (HANDOFF: "any O(1) error constant is FREE for
  `theorem_1_2`"); only `lhyC = 128/(15√π)` and the exponent `1/2 + η₀` with
  `η₀ < 1/1615` are rigid.  So the errors below are stated as "`C` times the
  bracket FS print", with `C` existential, and `Assembly.lean` absorbs them into
  the target's `K (μa³)^{1/2+η₀}` using `η₀ < 1/1615` and `t ≤ 1`.
* The normalisation `(2π)^{-3}ℓ³∫ dk ↔ Σ_k` over the mode lattice is B7's
  (`Work.BoseB7.Q3Defs` docstrings); the mode-indexed kernels `E.W1`, `E.tau`,
  `E.hatChi`, `E.hatChiSq` are the *sampled* values, as in that chapter.

## What is NOT here

Nothing in the `Work.BoseBox` `CSBox`/`boxWordU` vocabulary (refuted, see
`BOSE_BOXNODES_LEAD.md` §1).  The box side is
`Work.BoseKinLoc.BoxState` + `Work.BoseBoxFix.wordB`/`normB` only.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The diluteness and the box side, as local abbreviations -/

/-- FS's diluteness `t = μ a³` at the pair `(μ, a v)`. -/
def dil (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := μ * a v ^ 3

/-- FS's box side `ℓ = K_ℓ(μa)^{-1/2}` (the box side of the frozen vocabulary). -/
def ell (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := sideAt μ (a v)

/-- FS's box volume `ℓ³`. -/
def ell3 (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := ell v μ ^ 3

lemma ell_eq (v : ℝ³ → ℝ) (μ : ℝ) : ell v μ = sideAt μ (a v) := rfl

lemma ell3_eq (v : ℝ³ → ℝ) (μ : ℝ) : ell3 v μ = ell v μ ^ 3 := rfl

/-- FS's `X = (μa³)^{1/323}` at the pair `(μ, a v)`. -/
def fsX (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := fsXp (dil v μ) 1

/-- FS `eq:Xchoice`: the worst §11 error exponent `1/1615` (from `X^{1/5}`); with
`η₀ < 1/1615` this is what makes the §11 error of lower order than
`(μa³)^{1/2+η₀}`. -/
def errExp (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := (dil v μ) ^ (1 / 1615 : ℝ)

/-! ## 1. FS `eq:Kz`: the substituted Hamiltonian `𝒦(z)` on B4's mode lattice -/

/-- The `Q3Env` re-pointed at the condensate density `ρ = z²/ℓ³`: FS's `𝒦(z)`
depends on `z` through `z` itself, through `ρ_z = z²/ℓ³`, and through the kernels
`𝒜(k) = τ(k) + ρ_zŴ₁(k)`, `ℬ(k) = ρ_zŴ₁(k)` (`eq:SimplifyKz`).  Everything else
(`Ŵ₁ω`, `χ̂`, `χ̂²`, `f_L`, the parameters) is density-independent. -/
def KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) : Work.BoseB7.Q3Env Mode :=
  { E with
    z := Real.sqrt (ρ * E.ell ^ 3)
    A := fun k => E.tau k + ρ * E.W1 k
    B := fun k => ρ * E.W1 k }

/-- FS `eq:BogHamPositive-1`: the Bogoliubov quadratic `𝒦^Bog` at condensate
density `ρ`, as an operator on B4's mode lattice.

FS write `½(2π)^{-3}ℓ³∫[𝒜(k)(a_k†a_k + a_{−k}†a_{−k}) + ℬ(k)(a_k†a_{−k}† + a_ka_{−k})
+ 𝒞(k)(a_k†+a_{−k}†+a_k+a_{−k})]dk` with `𝒜(k) = τ(k) + ρ_zŴ₁(k)`,
`ℬ(k) = ρ_zŴ₁(k)`, `𝒞(k) = ℓ^{-3}(ρ_z−μ)Ŵ₁(0)χ̂_Λ(k)z`.  Summing the `∫ dk`
over the *whole* lattice turns the pair half into `Σ_{\text{pairs}}`: with the
weight `1/4` over all excited modes each pair `{k,−k}` is hit twice, giving
exactly `Σ_{pairs} ½·q_k` — the normalisation of `Work.BoseB6.BogHamInterface`
(its `decomp` field is `Kbog = Σ k, ½ * q k` over one representative per pair). -/
def KzBog {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    F.H →ₗ[ℝ] F.H :=
  let z : ℝ := Real.sqrt (ρ * E.ell ^ 3)
  ∑ k ∈ Work.BoseB7.excited Mode, (1 / 4 : ℝ) •
    ((E.tau k + ρ * E.W1 k) • (F.nOp k + F.nOp (-k))
      + (ρ * E.W1 k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
      + (E.ell ^ (-3 : ℝ) * (ρ - E.mu) * E.W1 0 * E.hatChi k * z) •
          (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)))

/-- The linear (`1Q`/`1Q^ex`) terms of FS `eq:Kz`/`eq:SimplifyKz`, combined:
`ρ_z z Ŵ₁ω(0)(2π)^{-3}∫χ̂²(s)(ã_s†+ã_s)ds
 + z(ρ_z−μ)Ŵ₁(0)(2π)^{-3}∫χ̂_Λ(k)(a_k†+a_k)dk`.

The `χ̂²` weight and the `h.c.`-in-one-operator shape are
`Work.BoseB7.linOp`'s (that is the form in which §10's `thm:Control3Q` bounds it);
the second summand is FS `eq:Kz`'s `𝒬₁(z)`, harmless by the same
Cauchy–Schwarz (`Work.BoseB7.linearTerm_bound`) and recorded here with the same
weight so that the two are controlled together. -/
def KzLin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    F.H →ₗ[ℝ] F.H :=
  (ρ * Real.sqrt (ρ * E.ell ^ 3) * E.W1omega0
      + (ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) •
    ∑ s ∈ Work.BoseB7.excited Mode, (E.hatChiSq s) • (F.aDag s + F.a s)

/-- **FS `eq:Kz`** — the substituted Hamiltonian `𝒦(z)` of `thm:Kafz` at
condensate density `ρ = z²/ℓ³`, on B4's mode lattice.

The six groups of terms, in FS's order (see `Work.BoseB7.Q3Defs` for the operator
names of §10):

1. the gap terms `(b/2ℓ²)n₊` and `ε_Tb/(2d²ℓ²)n₊^H`;
2. the `c`-number constant `½ρ_z²ℓ³(ĝ(0)+ĝω(0)) − μĝ(0)ρ_zℓ³`, in FS
   `eq:SimplifyKz`'s completed-square form
   `−½μ²ℓ³ĝ(0) + ½(ρ_z−μ)²ℓ³ĝ(0) + ½ρ_z²ℓ³ĝω(0)` (an exact rearrangement — FS's
   display) with `ĝω(0)` read as the environment's `Ŵ₁ω(0) = ∫W₁ω` (the two agree
   up to FS §4's `χ*χ` normalisation `W₁ = g/(χ*χ)`);
3. the Bogoliubov quadratic `𝒦^Bog` (`KzBog`);
4. the `(ρ_z−μ)Ŵ₁(0)` number term;
5. the linear term `T.linOpT (KzEnvAt E ρ)` (FS `eq:Kz`'s `𝒬₁^ex`, in the
   `θ`-mode form of the design, so that `T.controlWordT` matches term by term);
6. `Q₂^ex` and `Q₃(z)` (`Work.BoseB7.Q2ex`, `Work.BoseB7.Q3`), re-pointed at `ρ`
   through `KzEnvAt`.

`gHat0` is `ĝ(0) = ∫g`; at the level of the theorem it is `8π(a v)`
(`Submission.BoseGases`'s `∫g₀ = 8πa`), which is the identity that turns group 2's
`−½μ²ℓ³ĝ(0)` into FS's `−4πμ²aℓ³` of `eq:ToProve`. -/
def KzOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) :
    F.H →ₗ[ℝ] F.H :=
  ((E.b / (2 * E.ell ^ 2)) • T.N)
    + ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH)
    + ((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
        + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H))
    + KzBog F E ρ
    + (((ρ - E.mu) * E.W1 0) • F.nPlus)
    + T.linOpT (KzEnvAt E ρ)
    + F.Q2ex (KzEnvAt E ρ)
    + T.Q3T (KzEnvAt E ρ)

/-- **FS `thm:Kafz`: the substituted energy** at condensate density `ρ` — the
infimum of the quadratic form of `𝒦(z)` (`KzOp`) over the §6 spectral window
`eq:LocalizedAftercNumber` `1_{[0,𝓜]}(n₊)Φ = Φ`, normalised.

The window is `Work.BoseB7A.TildeData.NWindow` (`1_{[0,𝓜]}(n₊)Φ = Φ` in the
algebraic form of `BOSE_3Q_LEAD.md` §5: `Φ` is a finite sum of `n₊`-eigenvectors
with eigenvalues `≤ 𝓜`), i.e. FS `eq:LocalizedAftercNumber` with FS's *true*
`n₊ = T.N` — not `SpectLe`, and not `EstWindow`.  `f = 0` is always in the window
(`instNonemptyWindow`), so the infimum is over a nonempty index set; and since
Lean's `x / 0 = 0`, the index `f = 0` contributes `0` — harmless, because the
assembly only ever compares `KzVal` with *negative* bounds. -/
def KzVal {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) : ℝ :=
  ⨅ (f : {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}),
    F.qw f.1 (KzOp F T E gHat0 ρ) / F.normSq f.1

/-- `‖f‖² > 0` for `f ≠ 0` (`bp` is definite).  This is what lets the assembly
divide the homogeneous residual forms without any hypothesis on the sign of the
bound; it is why `KzVal` is taken over the **nonzero** window states (FS's `inf`
is over normalised `Φ`). -/
lemma normSq_pos {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) {f : F.H} (hf : f ≠ 0) : 0 < F.normSq f := by
  have h1 : 0 ≤ F.normSq f := F.bp_nonneg f
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd (F.bp_def f h.symm) hf

/-- `{ρ : ℝ // 0 ≤ ρ}` is nonempty (used by `le_ciInf` on the density infimum). -/
theorem nonemptyDensity : Nonempty {ρ : ℝ // 0 ≤ ρ} := ⟨⟨0, le_refl 0⟩⟩

/-! ## 2. The two density regions (FS `eq:Close-I` and `eq:Close`) and the two bounds -/

/-- FS `eq:Close-I` and `eq:Close`'s threshold, in the form in which §9/§10 use
it: `|ρ_z − μ| ≤ μK_ℓ^{-2}`.  (FS's own right-hand side is
`Cμ max((δ₁+δ₂+(μa³)/(K_ℓ^{6}(ds)^{6}))^{1/2}, (μa³)^{1/4})`, and `eq:NewConditionNew`
is exactly `K_ℓ²·max(…) ≤ C^{-1}`, i.e. FS's threshold *is* `μK_ℓ^{-2}` up to the
universal constant.  All constants here are free, so this is the faithful
normalisation of the two conditions; the child proving `RB5` receives FS's
`δ₁, δ₂` smallness through `Work.BoseBoxFix.Adm`'s `ParamsOK`.) -/
def closeThreshold (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ))

/-- `eq:Close`: `ρ_z` is close to `μ` (the regime in which §10 applies). -/
def CloseCond (v : ℝ³ → ℝ) (μ ρ : ℝ) : Prop := |ρ - μ| ≤ closeThreshold v μ

/-- `eq:Close-I`: `ρ_z` is far from `μ` (the regime in which `prop:FarAway`
applies). -/
def FarCond (v : ℝ³ → ℝ) (μ ρ : ℝ) : Prop := closeThreshold v μ ≤ |ρ - μ|

/-- FS `prop:FarAway`'s conclusion at the density `ρ`: the substituted energy is
at least `−4πμ²aℓ³` plus **twice** the LHY term `4π lhyC μ²aℓ³√(μa³)`. -/
def FarBound (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  -4 * π * μ ^ 2 * a v * ell3 v μ
    + 2 * (4 * π * lhyC * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ))

/-- FS `eq:Combined1`+`eq:Combined2`'s conclusion at the density `ρ`, with the
§11 errors `ℰ₁ + ℰ₂` of `eq:BogHamDiag`/`lem:BogIntegral`/`eq:Q3Cancels`:

`−4πμ²aℓ³ + 4π lhyC ρ²aℓ³√(ρa³) − C μ²aℓ³√(μa³)(X² + (R/a)²√(μa³) + X^{1/5})`.

The bracket is FS's `(X²𝓡 + (R²/a²)(μa³)^{1/2} + X^{1/5})`; the second-moment
constant `𝓡 v` is absorbed into `C` (`X²𝓡 ≤ C X²`, `𝓡` fixed).  The `ρ²` (rather
than FS's printed `ρ_z` in `eq:Combined1`) is the LHY term of `thm:LHY-Box`,
`4πρ²a·lhyC(ρa³)^{1/2}`, which at `ρ = μ` is FS `eq:EnergyBoxRes1`'s
`4πμ²a(128/15√π)(μa³)^{1/2}`. -/
def CloseBoundR (v : ℝ³ → ℝ) (R μ C ρ : ℝ) : ℝ :=
  -4 * π * μ ^ 2 * a v * ell3 v μ
    + 4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
    - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
        * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ)

/-- FS §8/§11's box-level error: the `thm:Kafz` error `Cμa` together with the
`prop:Hamilton2ndQuant` error
`Cμ²aℓ³√(μa³)((μa³)^{348/323−1/2} + X³(R/a)²(μa³)^{1/2})`, collected in one
bracket (all constants are free).

It is written with the `thm:Kafz` error in the form
`Cμa = Cμ²aℓ³√(μa³)·K_ℓ^{-3}` (FS's healing-length identity
`μa = μ²aℓ³√(μa³)K_ℓ^{-3}`), and `K_ℓ^{-3} = (μa³)^{9/646}`
(`Arith.Kl_inv_cube`); this makes the whole §11 arithmetic a comparison of
monomials in `μa³` (`Arith.errAbs`/`Arith.errKafz_eq_errAbs`), the only rigid
constants being `lhyC` and the exponents `{2/323, 1/2, 1/1615, 9/646}`. -/
def errKafz (v : ℝ³ → ℝ) (R μ C : ℝ) : ℝ :=
  C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
    * ((paramsAt μ (a v)).Kl ^ (-(3 : ℝ)) + fsX v μ ^ 2
        + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ)

/-! ## 3. The interface (`RView`, `KzDatum`) and the four residual `Prop`s -/

/-! ### FS §4–§6's kernels, as functions on momentum space

These are the *identifications* the view `RView` pins, so that the residual
`Prop`s `RB5`/`RB67` are statements about **FS's operator** and not about an
arbitrary realisation (a datum with free kernels can satisfy `RB4box` while
failing `RB5` — `RB5Residual_FINDING.md`).  The unambiguous ones are pinned here;
the four that need the Fourier conventions (`Ŵ₁`, `Ŵ₁ω`, `Ŵ₁ω(0)`, `χ̂`, `χ̂²`) are
recorded with their formulas and are to be pinned by the `BoseK15`/`BoseB4`
kernel instantiation (see `STATUS.md`), since getting their normalisation wrong
would make `Q3Kernel` unsatisfiable. -/

/-- FS `def:tau`: `(1−ε_T)[|k| − ½(sℓ)⁻¹]₊² + ε_T[|k| − ½(dsℓ)⁻¹]₊²`. -/
def tauFS (eT s d ℓ : ℝ) (k : ℝ³) : ℝ :=
  (1 - eT) * (max 0 (‖k‖ - (2 * s * ℓ)⁻¹)) ^ 2
    + eT * (max 0 (‖k‖ - (2 * d * s * ℓ)⁻¹)) ^ 2

/-- FS's low-momentum localisation `f_L(s) = f(‖k‖/(K_L√(μa)))` for a cut-off `f`
(`Work.BoseBoxFix.LowCut`: smooth, antitone, `1` on `(-∞,1]`, `0` on `[2,∞)`). -/
def fLFS (fc : Work.BoseBoxFix.LowCut) (KL μ a : ℝ) (k : ℝ³) : ℝ :=
  fc.f (‖k‖ / (KL * Real.sqrt (μ * a)))

/-- The `p`-convention Fourier transform `Ŵ(k) = ∫ e^{−i⟨k,y⟩}W(y)dy` of a real
function, as the real part of the corpus's `kinFT`. -/
def chat (W : ℝ³ → ℝ) (k : ℝ³) : ℝ :=
  (kinFT (fun y => ((W y : ℝ) : ℂ)) k).re

/-- FS §4's `W₁ = W(1−ω)` (the corpus's `wScaled ℓ (g0 v h)`). -/
def W1fun (v : ℝ³ → ℝ) (h : ScatSol v) (ℓ : ℝ) : ℝ³ → ℝ := wScaled ℓ (g0 v h)

/-- FS §4's `W₁ω = W(1−ω)ω` (`ω = w = Classical.choose h`, the corpus's scattering
solution: FS `eq:defW_12` has `W₁ = W(1−ω) = g/(χ*χ)` and `g = v(1−w)`, so
`1 − ω = 1 − w`, i.e. `ω = w`).

With the corpus's convention `W₁ = wScaled ℓ (g0 v h)` (`= g/(χ*χ(·/ℓ))`, `g = g0`)
this is `W(1−ω)ω = (g/(χ*χ))·ω = wScaled ℓ (g0 · w)`, i.e. the weight is the
scattering solution `w` itself — **not** `1 − w` (the earlier definition used
`g0 · (1−w)`, which is `W₁(1−ω)`, off by the factor `(1−w)/w`; it made the mass
cancellation `ĝω(0) = ∫W₁ω` — on which FS §9's `prop:FarAway` and §10's
`lem:BogIntegral` rest — fail, `RB5FSHonest`'s child: `RB5FS` is false with the
wrong kernel). -/
def W1omegaFun (v : ℝ³ → ℝ) (h : ScatSol v) (ℓ : ℝ) : ℝ³ → ℝ :=
  wScaled ℓ (fun z => g0 v h z * Classical.choose h z)

/-- FS §6's `χ_Λ` of the box `Λ = Λ(0)`: the corpus's `chiScale ℓ`.  FS's mode-indexed
`χ̂(kℓ)`, `χ̂²(kℓ)` are the **normalised** Fourier transforms of `χ_Λ`, `χ_Λ²`
(B7's `ccrKernel` convention `χ̂(0) = χ̂²(0) = 1`), which is why the pins in
`RView` divide by the value at `0`. -/
def chiFun (ℓ : ℝ) : ℝ³ → ℝ := chiScale ℓ

structure KzKernels (K₀ : ℝ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp : ∀ s, E.fL s ≠ 0 → F.PL E.KL E.mu E.aScat s
  kmom_sub : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → F.kmom (s - k) = F.kmom s - F.kmom k
  /-- **The guarded label identity.**  FS §10 only ever evaluates the commutator
  kernel on the pairs its sums run over (`i ∈ supp f_L ⊆ P_L`, `j ∈ P_H`); the
  *global* form is unsatisfiable on a finite mode group (`Work.BoseK15.Obstruction:
  `kmom (i-j) = kmom i - kmom j` for all `i,j` forces `kmom ≡ 0` and empties
  `P_H`), which is why this bundle — and not `Work.BoseB7A.Q3Kernel` — is the gate
  `RView` uses.  `Work.BoseK15.Guarded.hasKernel_guarded` proves it for the honest
  box model. -/
  hasKernel_guarded : ∀ i j : Mode, E.fL i ≠ 0 → j ∈ F.PHset E →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  /-- **Deviation from `BOSE_3Q_STATEMENTS.lean.txt`** (documented in the header):
  `χ̂` is even.  It is a true fact about the honest `χ_Λ` (and is what makes the
  two squeezed commutators `[b_{s−k},b_{−k}†]` and `[b_{−k},b_{s−k}†]` *equal*,
  hence `Q3T_split` true), and it is *not* derivable from the other fields, so it
  must be part of the interface. -/
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  /-- `χ̂²` is even (same reason; `Q3Kernel` is the only hypothesis of the three
  estimates, so everything they use has to be here). -/
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * Work.BoseB7A.eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * Work.BoseB7A.eta E
  /-- Bochner + `‖χ‖∞`: the kernel `χ̂²((s'−s)ℓ)` is PSD and `≤ K₀` (Schur form). -/
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H), (∀ s ∈ S, s ≠ 0) →
    0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) ∧
    ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s)
      ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s)
  count_PL : (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat
  alpha_lip : ∀ p q, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  /-- node `N-INT` (corrected `EstIntegralOne`). -/
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  /-- node `N-Q2` (first-quantised): `Q₂^ex` pays for the `T₂,comm` main term. -/
  q2exLower : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)

/-- **The view conditions**: the Fock datum `(F, E, gHat0)` *is* FS's §8–§10
datum at the box parameters `(v, h, μ)`.

These are the identifications B4's second quantisation
(`Work.BoseB4.b7FockDataBox`, imported here through `Submission.Work.BoseB4.All`)
and B7's parameter point
(`Work.BoseB7.FSParamsView`) supply; they are what makes `KzOp`'s formula the
correct `𝒦(z)`, and what a child proving `RB5`/`RB67` may assume.

Kernel-level identifications (`E.W1 k = Ŵ₁(k)`, `E.tau k = τ(k)`, `E.hatChi`,
`E.hatChiSq`, `E.fL` the §4 Fourier transforms, `E.W1omega`) are B4's obligation;
they can be added here without changing the shape of the four residual
statements. -/
def RView {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : Prop :=
  Nonempty (Work.BoseB7.FSParamsView E) ∧ E.mu = μ ∧ E.aScat = a v
    ∧ E.ell = ell v μ ∧ E.bigM = bigM (paramsAt μ (a v)) (a v) μ
    ∧ E.b = (paramsAt μ (a v)).b ∧ E.d = (paramsAt μ (a v)).d
    ∧ E.s = (paramsAt μ (a v)).s ∧ E.eT = (paramsAt μ (a v)).eT
    ∧ E.intM = (paramsAt μ (a v)).M ∧ gHat0 = 8 * π * a v
    -- FS's kinetic symbol and the kernel relations (`def:tau`, `eq:BogHamPositive-1`)
    ∧ E.tau = (fun k => tauFS (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
        (paramsAt μ (a v)).d (ell v μ) (F.kmom k))
    ∧ E.A = (fun k => E.tau k + E.rho * E.W1 k)
    ∧ E.B = (fun k => E.rho * E.W1 k)
    -- FS §4's Fourier kernels (`lem:DecaychiHat`, `eq:1Q-integral`)
    ∧ E.W1 = (fun k => chat (W1fun v h (ell v μ)) (F.kmom k))
    ∧ E.W1omega = (fun k => chat (W1omegaFun v h (ell v μ)) (F.kmom k))
    ∧ E.W1omega0 = chat (W1omegaFun v h (ell v μ)) 0
    -- `χ̂`, `χ̂²` are pinned to B4's **box kernel** (`Work.BoseB4.b7FockDataBox`,
    -- hence the Gram identity `hf` of every statement in this directory, and
    -- `Work.BoseK15.K15Input.hatChi_eq`/`hatChiSq_eq`): both are the Fourier
    -- transforms of `χ_ℓ = χ_Λ` divided by the **same** normaliser `∫χ_ℓ² = ℓ³`.
    -- For `χ̂` the "obvious" normaliser `χ̂(0) = 1` is *wrong*: it divides by
    -- `∫χ_ℓ = ℓ³∫χ`, while the box kernel carries `χ̂_Λ(k) = ∫ χ_Λ e^{ikx}dx`
    -- (whose value at `0` is `ℓ³∫χ`), so the `1/∫χ` mismatch makes the gate's
    -- `hasKernel_noWrap` row at the pair `(0,0)` a contradiction:
    -- `RView` would be **unsatisfiable** at the box data
    -- (`FINDING_bogopbound_honestfam_vacuous.md`,
    -- `RViewUninhabited.rview_unsat`).  With the normaliser `∫χ_ℓ² = ℓ³` the pin
    -- is definitionally `E.hatChi k = corpusBox.hatChi (ℓ • kmom k)`, which is
    -- what `K15Input` uses.
    ∧ E.hatChi = (fun k => chat (chiFun (ell v μ)) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ E.hatChiSq = (fun k =>
        chat (fun z => chiFun (ell v μ) z ^ 2) (F.kmom k)
          / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    -- FS's low-momentum cut-off
    ∧ (∃ fc : Work.BoseBoxFix.LowCut,
        E.fL = (fun k => fLFS fc E.KL E.mu E.aScat (F.kmom k)))
    -- **The χ-mode number is dominated by the interface's `N`.**  FS's `n₊` is *one*
    -- operator, written as `Σ_{k≠0}a_k†a_k` (χ-modes) or as `ℓ³(2π)⁻³∫ã†ã` (θ-modes);
    -- the interface keeps *both* realisations, the χ-mode sum `F.nPlus` (carried by
    -- `KzOp`'s term `((ρ−μ)Ŵ₁(0))•F.nPlus`) and the θ-mode operator `T.N` (the window
    -- `eq:LocalizedAftercNumber`, the gap `(b/2ℓ²)•T.N`).  This conjunct is the honest
    -- relation between them; the honest instance has it definitionally
    -- (`Work.BoseB4.tildeData`: `N = totNumOp ≥ Σ_{k≠0}a_k†a_k = F.nPlus`, the
    -- condensate mode being one more nonnegative summand).
    --
    -- It is *required*: it is what lets §9/§10 absorb the χ-mode term `(ρ−μ)Ŵ₁(0)⟨n₊⟩`
    -- into the gap and the window `⟨N⟩ ≤ 𝓜` (`Work.BoseB7A.NWindow_bp_N_le`); without
    -- it, `(ρ−μ)Ŵ₁(0)` would multiply an `⟨f,F.nPlus f⟩` unbounded on the window, and
    -- `RB5`/`RB67` would be unprovable (on the far region `ρ < μ` the coefficient is
    -- negative, and its *magnitude* — not only its sign — matters there).
    --
    -- It is *not* derivable from `FockData`/`TildeData`: the counterexample of
    -- `FINDING_canon_view_uninhabited.md` ADDENDUM (all χ-modes collapsing onto one
    -- oscillator: `nPlus = 3·a†a`, `N = a†a`) is admissible.  That is the reason to
    -- *state* it here, exactly as the kernel pinning is stated: the view says "this
    -- realisation is FS's datum", and FS's datum has `n₊ = N`.
    --
    -- **OPEN: the constant of this conjunct.**  The version with `Cn = 1` is the
    -- Bessel condition for the χ-mode family `ℓ^{-3/2}Q(e^{ikx}χ_Λ)`
    -- (`Σ_{i≠0}|Qu_i⟩⟨Qu_i| ≤ 1`), and at the corpus χ (`Submission.CubicChi`,
    -- `∫χ² = 1`, `χ(0) ≈ 2.31`) the frame constant is `‖χ_ℓ‖_∞² = χ(0)² ≈ 5.35 > 1`
    -- — machine-checked numerics in `RB4box/NOTE_RB4boxExistsCanon.md` §7.2 — so at
    -- B4's box data the conjunct *with* `Cn = 1` is **false**, and the view (hence
    -- every residual that takes it as an antecedent) is unsatisfiable there.  The
    -- faithful form is `∃ Cn, 0 ≤ Cn ∧ Cn ≤ CnMax ∧ ∀ f, …` with an *absolute* cap
    -- `CnMax` (the honest frame constant is scale-invariant); the cap is what lets
    -- the uniform error constants of `RB5`/`RB67` absorb the factor `Cn` of the
    -- `(ρ−μ)Ŵ₁(0)⟨n₊⟩` term.  See `STATUS.md` §"open interface repair" for the
    -- exact edit list; it is *not* applied here (it changes the two proved §10
    -- proofs and the delivered view lemmas).
    ∧ (∀ f : F.H, F.bp (F.nPlus f) f ≤ F.bp (T.N f) f)
    -- **The §10 kernel gate** (one absolute `K₀`) and `b₀ ≤ b`, on the close range.
    --
    -- It is `Work.BoseK15.Q3Kernel'` — BoseK15's *honest* bundle
    -- (`Submission/Work/BoseK15/GuardedKernel.lean`) — and **not** the local
    -- hand-copy `KzKernels` (still defined below): the `χ̂²`-PSD row is honest only
    -- for weights supported on `supp f_L` (the way §9/§10 use it, `c = f_L`), and
    -- the Bochner proof needs the label additivity on *non-wrapping* pairs
    -- (`Q3Kernel'.hasKernel_noWrap`), not the global additivity — which is
    -- refutable (`Work.BoseK15.Obstruction.kmom_eq_zero_of_add` empties `P_H`).
    -- `KzKernels`' *unguarded* `hatChiSq_form` (guarded only by `s ≠ 0`) is
    -- therefore **not** an honest fact, and gating the residuals on it would make
    -- them vacuous — precisely the trap of `RB5CanonView`'s child, which found
    -- that the honest PSD instance (`Work.BoseK15.hatChiSq_form_psd_guarded`)
    -- needs the `f_L` guard.  `Q3Kernel'` is satisfiable at the box data
    -- (`Work.BoseK15.Q3Kernel'_of_box`, from `K15Input` + `FSParamsView`).
    ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b
        ∧ ∀ ρ : ℝ, CloseCond v μ ρ → Work.BoseK15.Q3Kernel' K₀ F T (KzEnvAt E ρ))

/-- **The Fock realisation of the substituted Hamiltonian**: B4's mode-lattice
Fock system, B7's §10 parameter point and kernels, and the `c`-number constant
`ĝ(0) = ∫g`, bundled so that the four residual statements can quantify over
realisations (`RB4box` produces one; `RB5`/`RB67` must hold for every one that
satisfies the view `RView`).

The `Mode` type and its instances are *fields* (as in `Work.BoseB7.FockData`), so
that a realisation can be existentially quantified without universe ambiguity. -/
structure KzDatum where
  /-- the mode lattice of the box. -/
  Mode : Type
  [instAddCommGroup : AddCommGroup Mode]
  [instFintype : Fintype Mode]
  [instDecidableEq : DecidableEq Mode]
  /-- B4's Fock system on the mode lattice. -/
  F : Work.BoseB7.FockData.{0, 0} Mode
  /-- B7's §10 parameter point and mode-indexed kernels. -/
  E : Work.BoseB7.Q3Env Mode
  /-- FS `thm:Kafz`'s `ĝ(0) = ∫g` (`= 8πa v`). -/
  gHat0 : ℝ
  /-- **FS §10's second mode family** (`BOSE_3Q_LEAD.md` §5, `BOSE_3Q_STATEMENTS.lean.txt`):
  the `θ`-modes `ã_s = ℓ^{-3/2}a(Qe^{isx}θ)`, FS's true `n₊` (`N`) and `n₊^H` (`NH`),
  the number grading, and (through `Work.BoseB7A.TildeData.NWindow`) FS
  `eq:LocalizedAftercNumber`'s window `1_{[0,𝓜]}(n₊)`.  Built by
  `Submission/Work/BoseB7A` (`Work.BoseB7A.TildeData`); the design calls it
  `Work.Bose3Q.TildeData`. -/
  T : Work.BoseB7A.TildeData F

attribute [instance] KzDatum.instAddCommGroup KzDatum.instFintype KzDatum.instDecidableEq

/-- The substituted energy of a realisation. -/
def KzDatum.val (D : KzDatum) (ρ : ℝ) : ℝ := KzVal D.F D.T D.E D.gHat0 ρ

/-- The window of a realisation at the parameter `𝓜`. -/
def KzDatum.win (D : KzDatum) (f : D.F.H) : Prop := D.T.NWindow D.E.bigM f

/-- The view of a realisation at the box parameters. -/
def KzDatum.view (D : KzDatum) (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : Prop :=
  RView v h μ D.F D.T D.E D.gHat0

/-- **R-B4box** (FS §8: `prop:Hamilton2ndQuant`, `lem:2ndQuand`,
`lem:Q3-splitting2`, `thm:Kafz`): **the bridge from the symmetric box states to
the Fock interfaces.**

The realisation is a *family* `D : ℝ → KzDatum` indexed by the chemical
potential, because FS's box Hamiltonian `ℋ_Λ(μ)` — hence its second
quantisation — depends on `μ` through `ℓ(μ)` and *all* of `sec:params`'s
parameters; a single fixed `KzDatum` could satisfy the view `RView v μ ·` for at
most one `μ` (`RView` pins `E.mu = μ`), so `∃ D, ∀ μ, view` would be false.

For every low (`eq:aprioriPsi`) `n₊`-restricted (`eq:LocalizedAftercNumber`,
`Work.BoseBoxFix.SpectralNPlusLe`) symmetric box state `Φ` of
`Work.BoseKinLoc.BoxState n (sideAt μ (a v))`, the box word dominates the whole
substituted-energy family of `D`:

  `(⨅_{ρ ≥ 0} D.val ρ·‖Φ‖²) ≤ wordB v h μ n Φ + errKafz v R μ C·‖Φ‖²`

(the *homogeneous* form: FS's `Ψ̃` is normalised, so the error carries `‖Φ‖²`;
this is exactly what the assembly needs, since it lets the final comparison
`ℓ³Λ + errKafz ≤ D.val ρ` be multiplied by `‖Φ‖² ≥ 0` with no division),

and `D` carries a nonzero §6-window state (the `inf_z` of `thm:Kafz` is over
normalised `Φ`, so this is the nondegeneracy the assembly needs).

**The view `D.view v h μ` is required as a *conjunct*** (for every admissible `μ`),
not as an antecedent of the domination inequality: otherwise `RB4box … D` would
be satisfied vacuously by any junk realisation (e.g. `E.aScat ≠ a v`), and
`∃ D, RB4box … D` would be a triviality (reviewer's finding, this round).
`RB5`/`RB67` keep the view as an antecedent, because the assembly holds `D` fixed
and discharges it from this conjunct.

This is FS `eq:IntroK(z)` in the form "`wordB ≥ inf_{z} ⟨Φ(z),𝒦(z)Φ(z)⟩ − err`",
transported to `D.val` through
`inf_z ⟨Φ(z),𝒦(z)Φ(z)⟩ ≥ inf_z inf_{Φ'} ⟨Φ',𝒦(z)Φ'⟩`.  Its proof is the
15–30K-line R-B4box build (consuming `Work.BoseB4`'s `PLAN.md` items R1, R2, R3
and B7's `Q3Env`, and **fixing `D`'s kernels to FS §4's Fourier transforms** —
the `RView` docstring records what still has to be added there). -/
def RB4box (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (J : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    (∀ μ : ℝ, Adm v ε₀ μ → (D μ).view v h μ) ∧
    (∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        IsLowB v h J μ n Φ →
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
        (∃ f₀ : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f₀ ∧ f₀ ≠ 0) ∧
          (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (D μ).val ρ.1 * normB v μ n Φ)
            ≤ wordB v h μ n Φ + errKafz v R μ C * normB v μ n Φ)

/-- **R-B5** (FS §9: `lem:Roughbounds`, `prop:FarAway`): on the far region
`FarCond`, the substituted energy is at least `FarBound` (i.e. `−4πμ²aℓ³` plus
**twice** the LHY term).

Stated *at the fixed realisation family* `D` (not over all `D`: the kernels of
`Q3Env` are free data, so the bound is only meaningful for the family that
R-B4box exhibits).  The homogeneous form `bound · ‖f‖² ≤ ⟨f, 𝒦(z)f⟩` is used, so that the
statement needs no normalisation; the assembly divides by `‖f‖² > 0`
(`normSq_pos`, available because it infimises over the *nonzero* window states). -/
def RB5 (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).view v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → FarCond v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      FarBound v μ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOp (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- **R-B6/7** (FS §10 + §11's close case: `eq:SimplifyKz`, `thm:BogHamDiag`,
`lem:BogIntegral`, `thm:Control3Q`): on the close region `CloseCond`, the
substituted energy is at least `CloseBoundR`, i.e.

`−4πμ²aℓ³ + 4π lhyC ρ²aℓ³√(ρa³) − C μ²aℓ³√(μa³)(X² + (R/a)²√(μa³) + X^{1/5})`.

The two §11 errors are `ℰ₁` (`eq:Combined1`: §10's `lem:BogIntegral` error plus
the `(ρ_z−μ)²` term of `eq:SimplifyKz`) and `ℰ₂` (`eq:Combined2`:
`thm:Control3Q`, whose dominant contribution is `K_H^{-1}(μa³)^{5/12} = X^{1/5}`).
The child proves this by consuming **B6's `Work.BoseB6.bogHamDiag_fs`** (with
the `BogHamInterface` built from `KzBog`) and **B7's
`Work.BoseB7.Control3Q_at_fsParams`** (with `F`, `E`, `EstHyp F E` and the three
estimates). -/
def RB67 (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).view v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → CloseCond v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      CloseBoundR v R μ C ρ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOp (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-! ## 4. The API of the interface (used by the assembly)

`KzVal_le_of_bound`: a lower bound valid for every (nonzero) window state bounds
`KzVal`, by `le_ciInf`.  The index set is nonempty by hypothesis (the bridge
`RB4box` supplies a nonzero window state), and `normSq_pos` supplies the division
in the transition from the homogeneous residuals to normalised quotients. -/

lemma KzVal_le_of_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ)
    (hne : Nonempty {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0})
    {B : ℝ}
    (h : ∀ f : F.H, T.NWindow E.bigM f → f ≠ 0 →
      B * F.normSq f ≤ F.qw f (KzOp F T E gHat0 ρ)) :
    B ≤ KzVal F T E gHat0 ρ := by
  letI := hne
  refine le_ciInf fun f => ?_
  rw [le_div_iff₀ (normSq_pos F f.2.2)]
  exact h f.1 f.2.1 f.2.2

end Work.BoseFixR
