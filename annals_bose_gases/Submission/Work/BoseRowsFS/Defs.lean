import ChallengeDeps
import Submission.Work.BoseRowsFS.Hon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.Defs` — the three FS §11/§12 rows at the honest model

**Import note (2026-10-05).**  This file used to import
`Submission.Work.BoseGateFS.HonestGateFinal` for the abbreviations
`honE`/`honF`/`honT`.  That module is downstream of
`Submission.Work.BoseGateFS.GateHonest`, which is stale-broken (see `README.md`
§2bis), so the whole area was unbuildable by `lake build`.  The abbreviations are
re-declared with *the same bodies* in `Submission.Work.BoseRowsFS.Hon`, which
imports only modules upstream of the breakage; the definitions are definitionally
equal, so every statement below is literally the same term as before.

Subproject `Submission/Work/BoseRowsFS/` (area owner: curric-46).  The node
`Work.BoseGateFS` delivered `exists_honestGateFS_of_fsRows` /
`exists_honestGateFS`: the design's `HonestGateFS v h fc fu K₀ b₀` at one
absolute `(K₀, b₀)` from **three** genuine FS §11/§12 rows

* `hsumW1sq` — the weighted lattice sum of the UV-cut `Ŵ₁²` (FS `eq:I2-integral`);
* `hint`     — the integral row (FS `lem:EstimateIntegral`, `eq:CompIntegrals-Final`,
  the K5 row of the K15 bundle);
* `hq2`      — FS `eq:Q3Cancels`'s first-quantised `Q₂^ex` cancellation.

This module freezes those three rows as `Prop`-valued definitions in the
namespace `Work.BoseRowsFS`, with the **same** quantification as the gate's
hypotheses (so that `Work.BoseRowsFS.exists_honestGateFS_uncond` below is a pure
application of the gate's `exists_honestGateFS_of_fsRows`), and bundles them as
`FSRows`.

The point of the freeze is that the remaining mathematical content of the honest
gate is *one* named object, `FSRows v h fc fu R`, which a caller can hand to
`exists_honestGateFS_uncond` without knowing the gate's internals.

Conventions (the same as the gate's):
* `ℝ³ = EuclideanSpace ℝ (Fin 3)`;
* the honest data `honF`, `honT`, `honE` are the abbreviations of
  `Work.BoseGateFS.KinkInputHonest` for the family `HonestBoxFam v h fc fu HM`;
* `aScat = a v`, `ell = ellH v μ = sideAt μ (a v)`, and `W1 = ζ_{Λ_N}·Ŵ₁ ∘ kmom`;
* every constant is **absolute**: it may depend on the potential data
  `v, h, fc, fu, R` (which are fixed before the rows are stated) but never on the
  mode choice `HM`, the chemical potential `μ`, the cube size `N`, the density
  `ρ`, or the state.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowsFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases
open Work.BoseGateFS

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The three rows -/

/-- **FS §11 (`eq:I2-integral`), the weighted lattice sum of the honest `Ŵ₁²`.**

    `ℓ⁻³ Σ_{q ∈ P_H^q, q ≠ 0} W₁(q)²/‖q‖² ≤ Cws · a v`

at the honest data: the modes are those of the periodic cube `Lab N`, the sum is
over the `P_H^q` region (`‖q‖ ≥ ¼K_H⁻¹a⁻¹`) and `W₁ = ζ_{Λ_N}·Ŵ₁` is the UV-cut
kernel.  (`P_H^q` rather than `P_H` is what the gate's `Q3KernelFS.sum_W1sq`
asks; the summand is nonnegative, so the `P_H` form follows by monotonicity of
the sum over a sub-filter.)

The unweighted `L¹` form `Σ_{P_H^q} W₁² ≤ C·ℓ³a` is **false** for an arbitrary
nonnegative radial `v` — with `|Ŵ₁| ≤ 16πa` alone the sum behaves like
`a²K_Ha ≫ a` (`FINDINGS_honestRows.md` §2).  The honest content is the
Coulomb energy of the scattering solution: FS's identity
`(2π)⁻³∫Ŵ₁(p)²/(2‖p‖²)dp = ∫g₀ω·(1+O((R/ℓ)²)) ≤ 8πa(1+…)`
(`Work.BoseB7AK.C3Q.I2_integral_bound`). -/
def RowSumW1sq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R : ℝ) (Cws : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
            ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
              (honE v h fc fu HM μ).aScat),
          (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
      ≤ Cws * (honE v h fc fu HM μ).aScat

/-- **FS §11, `lem:EstimateIntegral` / `eq:CompIntegrals-Final` — the integral row**
(the K5 row of the K15 bundle).

    `|ρ Ŵ₁ω(0) − ℓ⁻³ Σ_{k ∈ P_H} W₁(k) α_k| ≤ Kint · ρ · a v · K_H⁻¹`

where `α_k = ℬ_k/(𝒜_k + √(𝒜_k²−ℬ_k²))` is the Bogoliubov squeezing parameter of
the environment `KzEnvAt (honE …) ρ` (so `𝒜 = τ̃ + ρW₁`, `ℬ = ρW₁`), at every
admissible density `ρ` (`AdmRho`: `0 ≤ ρ`, `μ/2 ≤ ρ ≤ 3μ/2`).

FS's own error is `Cρ_za(μa³)^{5/12}K_H⁻¹`; the row asks only for `ρ` in place of
`ρ_z` and an absolute constant, which is what the gate consumes.  FS's proof uses
the exact **mass identity** `Ŵ₁ω(0) = (2π)⁻³∫Ŵ₁(k)ĝ(k)/(2k²)dk` (`eq:W1-g` +
the Newton representation of `ω`) followed by the lattice⇄continuum comparison
of `Ŵ₁ĝ/(2k²)`. -/
def RowIntOne {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R : ℝ) (Kint : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
      |ρ * (honE v h fc fu HM μ).W1omega0
        - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
            (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
      ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹

/-- **FS §11's integral row in the dilute régime.**

The unrestricted form `RowIntOne` is **false** off the régime (`FINDINGS.md`
§1ter/§2): for `ℓ` below the sharp radius `R/chiR0` the honest kernel
`W₁ = g₀/(χ⋆χ)(·/ℓ)` can blow up like `σ^{-2}` on a thin annulus while the right
-hand side stays bounded.  Every honest statement of this row therefore carries
the caller's diluteness threshold `εg` in the antecedent, exactly as
`Work.BoseRowsFS.RowSumW1sq_regime` does for row 1. -/
def RowIntOneRegime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Kint : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
    ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
      |ρ * (honE v h fc fu HM μ).W1omega0
        - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
            (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
      ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹

/-- **FS §11's integral row in the dilute régime, at cube sizes `N ≥ Ng μ`.**

This is the shape in which the honest rows are actually available: every
generator of the honest `IntKernel` (and FS's own prescription for the UV cut)
needs `Ng μ ≤ N`, and `HonestModes.N` is a free field, so the restriction
`∀ μ, Ng μ ≤ (HM μ).N` is part of the statement and not a convenience. -/
def RowIntOneRegimeN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (Ng : ℝ → ℕ) (R εg : ℝ) (Kint : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ (μ : ℝ), 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        |ρ * (honE v h fc fu HM μ).W1omega0
          - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
              (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹

/-- **FS §12 (`eq:Q3Cancels`, l. 3240–3262) — the `Q₂^ex` cancellation.**

    `2ρ Ŵ₁ω(0) ⟨Ψ, G Ψ⟩ ≤ ⟨Ψ, Q₂^ex Ψ⟩ + (b/400) ⟨Ψ, gapOp Ψ⟩`

at the honest data, for every model vector `Ψ`.  `G = Σ_{s,s'∈excited}f_L(s)f_L(s')χ̂²(s'−s)ã_s'†ã_s`
is `T.Gop`, `Q₂^ex = Σ_{k∈excited}ρ(Ŵ₁ω(k)+Ŵ₁ω(0))a_k†a_k` is `F.Q2ex`, and
`gapOp = ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H` is `T.gapOpT`.

This is the row the `%%`-gate uses in its reserved form (`q2exLowerR`, which adds
the free reserve `½·dNumOpR` off `P_H^q`); the reserve is added by
`Work.BoseGateFS.Reserve.q2exLowerR_of_q2exLower`, so the unreserved form above is
what has to be proved. -/
def RowQ2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
      2 * ρ * (honE v h fc fu HM μ).W1omega0
          * (honF v h fc fu HM μ).qw Ψ
              ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
        ≤ (honF v h fc fu HM μ).qw Ψ
            ((honF v h fc fu HM μ).Q2ex (KzEnvAt (honE v h fc fu HM μ) ρ))
          + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
              ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))

/-! ## 2. The bundle -/

/-- **The three FS §11/§12 rows, at absolute constants.**  Everything the honest
gate still needs, in one object. -/
structure FSRows (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (R : ℝ) where
  Cws : ℝ
  Kint : ℝ
  Cws_nonneg : 0 ≤ Cws
  Kint_nonneg : 0 ≤ Kint
  sumW1sq : RowSumW1sq (h := h) (fc := fc) (fu := fu) R Cws
  intOne : RowIntOne (h := h) (fc := fc) (fu := fu) R Kint
  q2 : RowQ2 (h := h) (fc := fc) (fu := fu) R

end Work.BoseRowsFS
