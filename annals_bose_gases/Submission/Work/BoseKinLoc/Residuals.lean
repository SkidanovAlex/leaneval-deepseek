import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Residuals` — the named residuals of Node C

Node C (`BOSE_AUDIT_LEAD.md` §4, node C) needs FS `lem:LocKinEn`
(`∫_u𝒯_u du ≤ −Δ`) and FS `thm:CompareBoxEnergy` at the **decoupled** parameters.
`Defs.lean` fixes the vocabulary (`fsT`, `boxForm`, `EΛ`, the symbols).  This
module names the residuals into which FS/BS split `lem:LocKinEn`, so that they can
be proved independently and consumed by `kinetic_localisation_of_pieces`.

The four residuals are exactly the four ingredients of FS's proof (FS
`final_v2.tex` "Localization of the kinetic and potential energies", which follows
Brietzke–Solovej `arXiv:1901.00537`, Lemmas 3.3/3.7 = `lm:abskinloc`/`lm:kinloc`
and their `(44)`, `eq:Quav`, and Corollary `cl:Tusimple`):

| residual | FS / BS | content |
|---|---|---|
| `NeumannBound` | BS `eq:Neumannineq` = FS `(44)` | `∫_u(−Δ^N_u)(−Δ^N_u+(dℓ)⁻²)⁻¹du ≤ (−Δ)(−Δ+(dℓ)⁻²)⁻¹` |
| `GapBound β` | BS `eq:Quav` + Taylor | `∫_uQ_udu ≤ β⁻¹ℓ²p²/(ℓ²p²+β)` |
| `MomBound` | FS `eq:Q1Qslide` | `b∫_uQ_u1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_udu ≤ ½(−Δ)(−Δ+(dℓ)⁻²)⁻¹` |
| `TprimeBound β C` | BS `lm:kinloc` | the two-regime symbol `(|p|−½σℓ⁻¹)₊² + Cσp²/(p²+β)` |
| `AssemblySymbol β C` | BS `lm:Tu` final display | the pointwise budget `Σ ≤ p²` |

All five are stated at the **decoupled** parameters: `ℓ > 0` is free (`ℓ = ℓ(μ)`
in the application, `ℓ → ∞` allowed), no particle number and no large volume `L`
occurs anywhere, and the parameters `d, s, ε_T, b` are only bounded by a universal
constant.  Both audit tests pass: the constant state has `Q_uψ = 0`, hence every
residual is an equality `0 ≤ 0` there, and no hypothesis of the form
`∀ L ≥ 1, R ≤ L·c` occurs (the only radius condition in the chapter is `R ≤ ℓ·r₀`,
a *lower* bound on the free localisation scale `ℓ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc

open Submission.BoseGases
open Work.BSKinetic

open _root_.BoseGases

/-! ## 1. The four residuals and the assembly -/

/-- **BS `eq:Neumannineq` (FS's `(44)`)** at general `ℓ`: the `u`-average of the box
Neumann-resolvent fractions is dominated by the full-space fraction.  (BS prove it from
`Σ_{u∈ℤ³}(−Δ^N_u) = −Δ` on the ℤ³-tiling by form equivalence, the resolvent identity
`(A+a²)^{-1} ≤ (B+a²)^{-1}` for `A ≥ B`, and the averaging over the shift
`v ∈ [0,1]³`.) -/
def NeumannBound : Prop :=
  ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ ℓ d : ℝ, 0 < ℓ → 0 < d →
    Integrable (fun u : ℝ³ => neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ) →
      ∫ u : ℝ³, neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ ≤ raFrac ℓ d ψ

/-- **BS `eq:Quav`**: the `u`-average of the box mean-free mass is dominated by the
Fourier multiplier `β⁻¹ℓ²p²/(ℓ²p²+β)` (the Taylor expansion of `1−θ̂(ℓp)²` at `p = 0`). -/
def GapBound (β : ℝ) : Prop :=
  ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ ℓ : ℝ, 0 < ℓ →
    Integrable (fun u : ℝ³ => gapBare ℓ u ψ) →
      ∫ u : ℝ³, gapBare ℓ u ψ ≤ gapFrac ℓ β ψ

/-- **FS `eq:Q1Qslide`**: the large-momentum term is paid by half of the Neumann term,
for `b` smaller than a universal constant. -/
def MomBound : Prop :=
  ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ ℓ d : ℝ, 0 < ℓ → 0 < d → d ≤ 1 →
        Integrable (fun u : ℝ³ => momForm ℓ d u ψ) →
          b * (∫ u : ℝ³, momForm ℓ d u ψ) ≤ (1 / 2) * raFrac ℓ d ψ

/-- **The two-regime symbol of BS `lm:kinloc` (`eq:Fs`)** at scale `ℓ`, cutoff `σ`, with the
smoothness index `M = 5` of the corpus bump: the far-region branch `(|p|−½(σℓ)⁻¹)₊²` and the
near-region Taylor branch `Cσ^{M−2}‖p‖²`.  (The near-region branch is the one that controls the
`ℓ⁻²`-scale window excess at frequencies `‖p‖ ≍ 1/(σℓ)`; the *bounded* Taylor symbol of `eq:Quav`
does **not** — see `Tprime/REFUTATION.md`, where the bounded-only rendering is machine-refuted.) -/
def tprSym (ℓ σ C : ℝ) (p : ℝ³) : ℝ :=
  if (5 / 6) * (σ * ℓ)⁻¹ ≤ ‖p‖ then fsKinCoeff ((2 * (σ * ℓ))⁻¹) ‖p‖ else C * σ ^ 3 * ‖p‖ ^ 2

/-- **BS `lm:kinloc`** at general cutoff `σ`: the family form at the cut-off `(σℓ)⁻¹` is
dominated by the two-regime symbol `tprSym`. -/
def TprimeBound (C : ℝ) : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ s₀ →
    ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ ℓ : ℝ, 0 < ℓ →
        Integrable (fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff ((σ * ℓ)⁻¹)) u ψ) →
          ∫ u : ℝ³, bsOneBody ℓ (fsKinCoeff ((σ * ℓ)⁻¹)) u ψ ≤
            ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, tprSym ℓ σ C p * ‖fhat ψ p‖ ^ 2

/-- **BS `lm:Tu`'s final symbol inequality** (with FS's replacement of the `ε_T`-fraction
by the half plus the large-momentum term): the pointwise budget in momentum space,
`ε_T(dℓ)⁻²(−Δ)(−Δ+(dℓ)⁻²)⁻¹ + bβ⁻¹ℓ²p²/(ℓ²p²+β) + (the two `T'`-symbols at `σ = 2s`, `2ds`) ≤ p²`. -/
def AssemblySymbol (β C : ℝ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ℓ d s εT b : ℝ, KinRegime c₀ ℓ d s εT b →
    ∀ p : ℝ³,
      εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p
        + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        + ((1 - εT) * tprSym ℓ (2 * s) C p + εT * tprSym ℓ (2 * (d * s)) C p)
      ≤ ‖p‖ ^ 2

/-- **The `AssemblySymbol` budget at an explicit regime constant `c`.**  This is the form in
which the `b`-threshold is a *parameter* instead of an existential: FS fixes `b = 1/16`
downstream, but the admissible `b`-range is bump-dependent (see README §11), so the budget has to
be stated at the explicit regime `KinRegime c` and discharged for the `c` wanted. -/
def AssemblySymbolAt (β C c : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ 0 < C ∧ ∀ ℓ d s εT b : ℝ, KinRegime c ℓ d s εT b →
    ∀ p : ℝ³,
      εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p
        + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        + ((1 - εT) * tprSym ℓ (2 * s) C p + εT * tprSym ℓ (2 * (d * s)) C p)
      ≤ ‖p‖ ^ 2

/-- **FS `lem:LocKinEn`** in the form the chapter consumes: `∫_u𝒯_udu ≤ −Δ` at the
decoupled parameters. -/
def KineticLocalisation (c₀ : ℝ) : Prop :=
  ∀ ℓ d s εT b : ℝ, KinRegime c₀ ℓ d s εT b → ∀ ψ : ℝ³ → ℝ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun u : ℝ³ => fsT ℓ d s εT b u ψ) →
        ∫ u : ℝ³, fsT ℓ d s εT b u ψ ≤ dSpace ψ

end Work.BoseKinLoc
