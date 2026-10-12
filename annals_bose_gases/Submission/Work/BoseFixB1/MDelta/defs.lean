import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.slidingBogPortCube
import Submission.Work.BoseFixB1S.slidingNewtonMassSharpB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.MDelta.defs` — the exact accounting of the per-box ledger, and the
# *sharpened* (`MΔ`-payer) Bogoliubov port

## 1. The accounting (this is what the file records)

The per-box row of FS `thm:smallbox` is the fleet's residual, in the matched-window spelling
(`chiSmallB`, cube kernels, ball-free spectral slot — `sbWordCube`,
`Work.BoseFixB1B.sbWordCube_ge_sharpRung`, PROVED):

    sbWordCube ≥ a0MainLocBox(V,μ,M₁,S) + boxA2 + cubeSpectral
                  + ½(M₂/V²)·Pc − ¼(M₁/V²)·(Pc + S² − S) .                     (R)

For an in-box normalised state (`S = n`, `Pc = n(n−1)`, `Pc + S² − S = 2Pc`, `bI = 1`) the two
`M₁`-rows cancel **exactly** and (R) reads

    sbWordCube ≥ a0 + [boxA2 + cubeSpectral] + ½(MΔ/V²)·Pc ,   MΔ := M₂ − M₁ ,   (R')

and the target row is `a0' − C·rows ≤ sbWordCube` where `a0'` differs from `a0` only by the
`O(1/V)` defect rows of `a0MainLocBox`.  Hence the *whole* residual is a lower bound on

    S := boxA2 + cubeSpectral

of the form `S ≥ −½·X·((n+1)n/V²)·bI − C·rows` for some payer `X` — and the shrinking of `X` is
the whole content:

* `X = D·χ_m`  (`D = g0w0Mass = ∫g₀ω₀`, FS's `eq:refinedaprioribog` payer, the *commutator* payer
  `[b_p,b_p†] ≤ n₀|B|⁻¹∫χ_B²`): **PROVED** (`Work.BoseFixB1B.scaledBogPortCube`,
  `…scaledBogPortCubeEta` here for every `0 < η ≤ 16`, `…slidingBogPort_proved` for `η = 8K_s+1`).
  It closes the ledger **iff `MΔ ≥ (1+δ)·D·χ_m`** — FS's `eq:w>g` — which the fleet has **refuted**
  at the corpus's two-factor cutoff (`FINDING_w2w1CubeComparisons_FALSE.md`: for a needle against
  the `ℓ`-face, `MΔ ≤ 2.01θ(R)ĝω(0)χ_m ≪ D·χ_m`).
* `X = MΔ` (**the sharpened port**, `MDeltaPort` below): then `½(MΔ/V²)Pc − ½MΔ((n+1)n/V²)bI`
  is `−MΔ·ρ/V` — a `1/(n)` row — and the ledger closes **with no mass comparison at all** (the
  sibling's `FINDING_sbWordCube_ge_meanFieldRow.md` §2 records exactly this).  This is the
  correct residual, and it is *strictly stronger* than the proved ports: `MDeltaPort` +
  `MassUpper` **imply** the `D·χ_m`-payer port with the same `η` (`scaledBogPort_of_mDeltaPort`
  below), so no proved port can replace it (the implication is one-way: the reverse needs the
  refuted `eq:w>g`).

## 2. What is *proved* here

* `bMDelta` — the mass difference, `MΔ = bM2 − bM1`.
* `scaledBogPortCubeEta` (`MDelta/bogPortEta.lean`, PROVED, axiom-clean) — the sliding Bogoliubov
  port at the cube window with an **arbitrary prescribed** `0 < η ≤ 16`.  The corpus's
  `Work.BoseFixB1B.scaledBogPortCube` only allows `η ≤ 1/10`; the `η/4 ↦ η/16` re-parametrisation
  of `δ` (with the same three-factor `hExt` estimate) widens it, which is what a consumer needing a
  *larger* prescribed `η` (e.g. to absorb a mass-row comparison) has to have.
* `MassUpper v h η` — the **upper** mass estimate `MΔ ≤ (1+η)D·χ_m + η(a v)χ_m`.  This is the
  *Cauchy–Schwarz/flatness* direction of `lm:w2>w1` (the autocorrelation of `χ_B` is at most
  `(1+η)` times the corpus's factorised denominator `convScaleSmall·convScale`; the only constant
  is `1/convScale ℓ ≤ 2` by `Work.BoseGases.convScale_ge_half_ball`), **not** the refuted lower
  direction.  It is the arithmetic input of `scaledBogPort_of_mDeltaPort`, and the honest residual
  of this file's lane.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.UBB Work.BoseBox
  Work.BoseBoxFix

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The mass difference `MΔ = M₂ − M₁`** of FS `lm:w2>w1` at the sliding box.  By
`w2_sub_w1_pointwise`-type unfolding it is the `ω`-weighted autocorrelation

    MΔ = ∬_{B(u)×B(u)} χ_B(x)·(g₀ω₀)(x−y)/E(x−y)·χ_B(y) dx dy ,

`E = convScaleSmall M (ℓd)·convScale ℓ` the corpus's renormalisation denominator. -/
noncomputable def bMDelta (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) : ℝ :=
  bM2 v h μ u - bM1 v h μ u

/-- **The `MΔ`-mass *upper* bound** (`lm:w2>w1`'s autocorrelation estimate in the direction that is
*not* refuted): there is a diluteness threshold such that on the good set

    MΔ ≤ (1+η)·(g₀ω₀-mass)·χ_mass + η·(a v)·χ_mass .

Cauchy–Schwarz (`∬χ(x)χ(y)k(x−y)dxdy ≤ χ_mass·∫k` for `k ≥ 0`) reduces it to the statement that the
corpus's factorised denominator `convScaleSmall·convScale` dominates the autocorrelation of `χ_B`
up to `1+η`; the `ℓ`-factor costs at most `2` (`convScale ≥ 1/2` on `ball 0 R`,
`Work.BoseGases.convScale_ge_half_ball`), and the `dℓ`-factor cancels against the same factor in
`χ_mass`.  `η = 1` is expected; `η = 16` is what this lane asks for, to leave room for the
transition-zone constants.  (Contrast `eq:w>g`, the *lower* bound `MΔ ≥ (1−θ)D·χ_m`, which is the
statement that the autocorrelation is *maximal* and is FALSE for a needle against the `ℓ`-face.) -/
def MassUpper (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (η : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3, u ∈ goodSet (bSide v μ) (bD v μ) μ →
      bMDelta v h μ u
        ≤ (1 + η) * Submission.BoseGases.g0w0Mass h
            * chiMass (bM v μ) (bSide v μ) (bD v μ) u
          + η * (_root_.BoseGases.a v) * chiMass (bM v μ) (bSide v μ) (bD v μ) u

/-- **The *sharpened* (payer `MΔ`) sliding Bogoliubov port** — the exact instrument the per-box
ledger of §1 needs, and the residual of this lane:

    0 ≤ ½·MΔ·((n+1)n/V²)·bI + bSpectralCube + bA2 + C·a·(μ + n/V)·bQ + C·a·μ·bI .

It is *strictly stronger* than the proved `D·χ_m`-payer ports (see
`scaledBogPort_of_mDeltaPort`); with it, (R′) closes to the target row with the leftover
`½(MΔ/V²)·(Pc − (n+1)n·bI) = −MΔ·ρ`-scale term, i.e. with **no** mass comparison `MΔ ≥ D·χ_m`. -/
def MDeltaPort (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : E3),
      u ∈ goodSet (bSide v μ) (bD v μ) μ →
      0 ≤ (1 / 2) * bMDelta v h μ u
            * ((((n : ℝ) + 1) * (n : ℝ)) / (bV v μ u) ^ 2) * bI v μ (Φ : X n → ℝ)
        + Work.BoseFixB1S.bSpectralCube v μ (Φ : X n → ℝ) u
        + bA2 v h μ (Φ : X n → ℝ) u
        + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / bV v μ u) * bQ v μ (Φ : X n → ℝ) u
        + C * (_root_.BoseGases.a v) * μ * bI v μ (Φ : X n → ℝ)

/-- **`MDeltaPort` + `MassUpper` reproduce the `D·χ_m`-payer port** — the one-way implication
that makes `MDeltaPort` the residual: the sharpened port's payer `MΔ` is dominated by
`(1+η)·D·χ_m + η·a·χ_m`, and enlarging the payer only *weakens* the lower bound, so the
`(1+η)`-port follows.  (The reverse implication would need `MΔ ≥ (1+η)D·χ_m` — the refuted
`eq:w>g` — and is therefore *not* available: no proved `D·χ_m`-payer port can replace
`MDeltaPort`.) -/
theorem scaledBogPort_of_mDeltaPort {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {η : ℝ}
    (hMU : MassUpper v h η) (hMP : MDeltaPort v h) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : E3),
        u ∈ goodSet (bSide v μ) (bD v μ) μ →
        0 ≤ (1 / 2) * ((1 + η) * Submission.BoseGases.g0w0Mass h
                + η * (_root_.BoseGases.a v))
              * ((((n : ℝ) + 1) * (n : ℝ)) / (bV v μ u) ^ 2) * bI v μ (Φ : X n → ℝ)
              * chiMass (bM v μ) (bSide v μ) (bD v μ) u
          + Work.BoseFixB1S.bSpectralCube v μ (Φ : X n → ℝ) u
          + bA2 v h μ (Φ : X n → ℝ) u
          + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / bV v μ u) * bQ v μ (Φ : X n → ℝ) u
          + C * (_root_.BoseGases.a v) * μ * bI v μ (Φ : X n → ℝ) := by
  obtain ⟨εM, hεM, hM⟩ := hMU
  obtain ⟨εP, CP, hεP, hCP, hP⟩ := hMP
  refine ⟨min εM εP, CP, lt_min hεM hεP, hCP, ?_⟩
  intro μ hAdm n Φ u hu
  have hAdmM : Work.BoseBoxFix.Adm v εM μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmP : Work.BoseBoxFix.Adm v εP μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hMμ := hM μ hAdmM u hu
  have hPμ := hP μ hAdmP n Φ u hu
  set χM : ℝ := chiMass (bM v μ) (bSide v μ) (bD v μ) u with hχM
  set Ib : ℝ := bI v μ (Φ : X n → ℝ) with hIb
  set Xr : ℝ := ((((n : ℝ) + 1) * (n : ℝ)) / (bV v μ u) ^ 2) with hXr
  have hχnn : 0 ≤ χM := chiMass_nonneg _ _ _ _
  have hInn : 0 ≤ Ib := Work.BoseFixB1.bI_nonneg v μ _
  have hXnn : 0 ≤ Xr := by
    rw [hXr]
    exact div_nonneg (mul_nonneg (by positivity) (by positivity)) (sq_nonneg _)
  -- `MΔ ≤ ((1+η)D + ηa)·χ_m`, so the sharpened row is dominated by the `Dχ_m` row
  have hstep : (1 / 2) * bMDelta v h μ u * Xr * Ib
      ≤ (1 / 2) * ((1 + η) * Submission.BoseGases.g0w0Mass (v := v) h
            + η * (_root_.BoseGases.a v)) * Xr * Ib * χM := by
    have h1 : bMDelta v h μ u ≤ ((1 + η) * Submission.BoseGases.g0w0Mass (v := v) h
        + η * (_root_.BoseGases.a v)) * χM := by
      rw [add_mul]; linarith [hMμ]
    have h2 : 0 ≤ (1 / 2) * Xr * Ib := by positivity
    nlinarith [h1, h2]
  linarith [hPμ, hstep]

end Work.BoseFixB1
