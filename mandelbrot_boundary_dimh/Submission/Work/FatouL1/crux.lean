import Mathlib
import Submission.Work.Interfaces.FatouNarrow

/-!
# FATOU-L1: the single remaining mathematical gap

## State of the area (verified: the closure of `Work.FatouL1.fatouL1` has exactly one `sorry`,
namely the placeholder for `FatouCoordExistsL1`, no forbidden module, `Unif2 = 31`)

Everything in the narrow (`L¹`) FATOU area is now **proved** except the existence, for every
near-translation `F` on Shishikura's region `𝒬 = Qreg b₁ b₂` whose derivative defect is `L¹`
along the vertical lines of `𝒬`, of **one** Fatou coordinate `Φ`: holomorphic and injective on
`𝒬` with the Abel equation `Φ (F z) = Φ z + 1`.  Nothing quantitative is required — no bound on
`Φ'`, no surjectivity modulo `ℤ`, no orbit relation.

## Why this is the only gap

Let `x₀` be the centre produced by `Work.FatouL1.exists_wideStrip hadm`, `W = wStrip x₀ =
{x₀ - 1/8 < Re < x₀ + 17/8}` the wide strip (all its vertical lines lie in `𝒬`), and

`ChartOnWide F x₀` (defined in `Work.FatouL1.assembly`): there is a holomorphic injective `φ` on
`W` with `φ (F z) = φ z + 1` on the overlap and `‖deriv φ z - 1‖ ≤ 1/8` on `W`.

The following chain is complete, in this directory, and closure-clean:

* `Work.FatouL1.fatouSecondDerivWideBound` — from `Φ` one obtains a Fatou coordinate with
  `‖iteratedDeriv 2 Φ‖ ≤ 1/100` on `W` (the `Φ` it uses is `Work.FatouL1.fatouCoord`, whose
  *definition* is the only place the existence of a coordinate is consumed);
* `Work.FatouL1.cocycleCorrectionWide` — hence the multiplicative cocycle
  `σ (F z) = F'(z) σ z` on the overlap, with `‖σ - 1‖ ≤ 1/31` and `‖σ⁻¹ - 1‖ ≤ 1/31` on `W`;
* `Work.FatouL1.localAbelWide_of_pieces` — hence, for a preconnected overlap, the Abel chart on
  `W`, i.e. exactly `ChartOnWide F x₀`;
* `Work.FatouL1.hasFatouCoordOrbitL1_of_chart` — hence `HasFatouCoordOrbitL1 b₁ b₂ F`, whose first
  component is `IsFatouCoordOn F Φ 𝒬`;
* `Work.FatouL1.fatouStatementL1_of_chart` — hence the whole contract `FatouStatementL1`.

`Work.FatouL1.fatouL1` is proved by running this chain, and **all** of its inputs are theorems
already in the tree.  The only thing that could not be produced cleanly is the existence of `Φ`
itself: every module of the tree that supplies one
(`Work.FatouCH.fatouCH`, `Work.Fatou.FX8.*`) goes through the uniformization library, which the
project lead's import budget forbids for this area.

## Recommended route to `FatouCoordExistsL1`

It suffices to prove the *multiplicative cocycle* on the wide strip (this is the form in which
the analytic content is clean, Φ-free and weight-free; it is the statement of the existing,
currently-unclean `Work.FatouL1.cocycleCorrectionWide`):

  `∃ σ : ℂ → ℂ`, `DifferentiableOn ℂ σ (wStrip x₀)`,
  `σ (F z) = deriv F z * σ z` for `z, F z ∈ wStrip x₀`,
  `‖σ z - 1‖ ≤ 1/31` and `‖(σ z)⁻¹ - 1‖ ≤ 1/31` for `z ∈ wStrip x₀`

and then feed it to `Work.FatouL1.localAbelWide_of_pieces` (proved) with
`Work.FatouL1.overlapPreconnectedWide` (proved) to get `ChartOnWide F x₀`, and extract `Φ` from
`Work.FatouL1.hasFatouCoordOrbitL1_of_chart`.  Tools available (all proved, all in this
directory): `Work.FatouL1.logDerivBound` (‖log F'‖ ≤ 1/31 and line mass ≤ 1/62 on `W`),
`Work.FatouL1.hcSolverBound`/`hcSolverDifference` (the Cauchy–Heine inverse of the *unit* shift
with a mass bound), `Work.FatouL1.primitiveOnStrip`, `Work.FatouL1.wideDerivSmall`
(‖F' - 1‖ ≤ 1/150 on `W`), `Work.FatouL1.secondDerivLineBound`, `Work.FatouL1.pointwiseDerivBound`.

Two remarks that may save time:

* Write `v := F - id` (`‖v - 1‖ ≤ 1/32`), `g := F' - 1` and `σ = v (1 + ρ)`.  Then the
  cocycle for `σ` is *exactly*
  `ρ (F z) = (ρ(z) - μ(z)) / (1 + μ(z))`, i.e. `log (1 + ρ)` is a `Δ_F`-primitive of
  `-log (1 + μ)`, where `μ := (M₁g - g)/(1 + g)`, `M₁g(z) := ∫₀¹ g (z + t v(z)) dt`.  Reason:
  `v (F z) = v(z) ∫₀¹ F' (z + t v(z)) dt = v(z) (1 + M₁g(z))` while
  `F'(z) v(z) = (1 + g(z)) v(z)`, so `v (F z) = F'(z) v(z) (1 + μ(z))` with
  `μ = (M₁g - g)/(1 + g)`.
* The datum `μ` is *tiny*: `|M₁g - g| ≤ (1/2) ‖g'‖ ‖v‖ ≤ (1/2)(1/280)(33/32) ≈ 1.8·10⁻³` on `W`
  (`g' = F''`, and `‖F''‖ ≤ 1/280` on `W`) and `|1 + g| ≥ 31/32`, so `|μ| ≤ 2·10⁻³`; `μ` also has
  bounded line mass (`lineMassDerivLe`) and (to first order) vanishing mean.  So the problem
  becomes a *linear* one, `Δ_F ρ = -μ` plus a quadratic correction, with a small explicit datum —
  no linear growth in `|Im|` occurs in this formulation.
* Any route that estimates a *difference* of competitors in the `ζ`-coordinate of a conjugacy
  `ψ (ζ+1) = F (ψ ζ)` runs into a linear growth in `|Im ζ|`; this is exactly why
  `MandelDim.WeightedL1` exists — but the *cocycle* formulation above does not need it.

## The project lead's constant chain (session 13) — and the one gap in it

The lead's budget: `σ = v(1+ρ)`, `v = F - id`, `‖v - 1‖ ≤ 1/32`, so
`‖σ - 1‖ ≤ 1/32 + (33/32)|ρ|`, and `‖σ - 1‖ ≤ 1/26` needs `|ρ| ≤ (1/26 - 1/32)(32/33) = 0.00699`.

1. **Exact identity.**  `μ := v(F z)/(F'(z) v(z)) - 1 = [∫₀¹ (F'(z + t v(z)) - F'(z)) dt] / F'(z)`
   (because `F(z+v) - F(z) = ∫₀¹ F'(z+tv) v dt`), so
   `|μ(z)| ≤ (32/31)(33/32)·½·sup_{segment}|F''|`.
2. **Mass of `F''` from the `L¹` hypothesis** (Cauchy on circles of radius `r`, then Tonelli):
   `∫ |F''(x+iy)| dy ≤ (1/r)·(1/64)`.  All vertical lines within distance `r` of the swept region
   must lie in `Qreg`; the wide strip has width `9/4` inside a waist of width `> 4`, so a *centred*
   `x₀` leaves `7/8` on each side: take `r = 3/4` and get `mass(F'') ≤ (4/3)(1/64) = 1/48`.
   (`Work.FatouL1.lineMassDerivLe` is this statement, already proved; `exists_wideStrip` may need
   re-centring: one wants `Re b₁ + 7/8 < x₀ - 1/8` and `x₀ + 17/8 + 7/8 < Re b₂`.)
3. `mass(μ) ≤ (32/31)(33/32)(1/2)(1/48)(1 + 1/150) ≈ 0.0111`.
4. `|log(1+ρ)| ≤ ½·mass(log(1+μ)) ≈ 0.00562`, so `|ρ| ≤ 0.00564 < 0.00699`, hence
   `‖σ - 1‖ ≤ 0.0371 < 1/26`; also `‖σ⁻¹ - 1‖ ≤ ‖σ-1‖/(1-‖σ-1‖)`.

**Where the chain needs care.**  Step 4 inverts the *unit* shift: `hcSolver h (z+1) - hcSolver h z =
-h z` (`Work.FatouL1.hcSolverDifference`), whereas the equation for `ρ` is the **`F`-shift**
`ρ(F z)(1+μ) = ρ(z) - μ`, i.e. `Δ_F log(1+ρ) = -log(1+μ)`.  The two operators differ by
`(Δ_F - Δ₁) = [U(F z) - U(z+1)] ≈ ε(z)U'(z+1)` with `ε = F - id - 1` (`‖ε‖ ≤ 1/32`); the defect is
*pointwise* tiny (≈ `3·10⁻⁴`) but `ε` does not decay in `Im`, so the defect has no *a priori* mass
bound and `hcSolver` cannot be iterated naively.  Two ways out:

* **`ζ`-formulation.**  In the conjugate variable the equation *is* the unit shift: if
  `ψ(ζ+1) = F(ψ ζ)` then `g := log ψ'` satisfies `Δ₁ g = log F' ∘ ψ`.  The mass of the datum is
  now available: `Work.FatouL1.massLogDerivComp` (PROVED) gives
  `mass(log F' ∘ ψ) ≤ 1/10` whenever `‖ψ' - 1‖ ≤ 1/9` and `ψ` maps the strip into the waist —
  the curve-to-line transfer (`curveReduction` + `curveMassLipschitzGraph`) is done.  The price is
  that the *difference* `δψ = ∫(e^g - e^{g'})` grows linearly in `|Im|`, so the contraction in the
  sup norm does not close; that is precisely what `MandelDim.WeightedL1` was introduced for.
* **Stay with `Δ_F`** and control the defect directly: iterate
  `U_{n+1} := hcSolver (-(f - [U_n(F z) - U_n(z+1)]))` in a norm that keeps the defect's mass
  finite (the defect decays like `U'` does if `U` does), or use the left-recursion
  `U(z) := U(F^{-1}z) + f(F^{-1}z)` on the overlap together with the holomorphy across the seam.

## How much slack is there? (do not over-engineer)

`Work.FatouL1.localAbelWide_of_inputs` accepts `‖σ - 1‖ ≤ 1/31` and `‖σ⁻¹ - 1‖ ≤ 1/31` and returns
`‖φ' - 1‖ ≤ 3/29`; `ChartOnWide` only asks for `1/8`.  Re-running that elementary chain shows the
method tolerates `‖σ - 1‖ ≤ 1/26` (giving `≈ 0.121`) but *not* `1/25` (`≈ 0.125`), because the
normalisation discrepancy `|c - 1| ≤ (δ/(1-δ))(33/32) + 1/32` is dominated by the fixed `1/32` of
`NearTranslationOn`.  So a proof of the cocycle must be accurate to within a factor `≈ 30` of the
truth `‖σ - 1‖ ≈ 1/31` (the numerics of `NOTES_cocycleCorrection_s6.md` show the truth is sharp).
Crude chains (`‖σ - 1‖ ≤ ‖g‖ + ‖g'‖/2 ≈ 1/16`, or `‖ρ‖ ≤ mass(μ)/2 ≈ 1/62` in the flow-model
formulation below) are **too lossy**; any successful route has to use the structure (the
vanishing of the resonant part), not just pointwise/mass boundedness.

## Import budget (hard rule of the project lead)

The final closure must NOT contain `Submission.Lib.UnifWrapper`,
`Submission.Lib.Unif2.Work.{Drive,SimplyConnected,Spine}.*`, `Submission.Work.Fatou.FX8.*`,
`Submission.Work.Fatou.Surface.*`, or `Submission.Work.FatouCH.{existsSetup, fatouExists, fatouCH,
noHalfPlane, Setup, phiHolo, fatouPhiHolo}`.  In particular do **not** import
`Submission.Work.FatouCH.fatouCH` (nor `...FX8.Assembly`, which it pulls in).  Use the
re-homed copies under `Submission.Work.FatouL1.Surface.*` if the orbit data is needed.
-/

open MandelDim

namespace Work.FatouL1

noncomputable section

/-- **THE REMAINING GAP.**  Existence of a Fatou coordinate (qualitative: no derivative bound,
no surjectivity modulo `ℤ`, no orbit relation) for a near-translation on an admissible
Shishikura region, under the `L¹` hypothesis on the vertical lines. -/
def FatouCoordExistsL1 : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), MandelDim.QAdm b₁ b₂ →
    MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂) →
    ∃ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)

end

end Work.FatouL1
