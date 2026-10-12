import ChallengeDeps
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Defs` — the `Q3KernelFSAll` gate vocabulary

`BOSE_ALL_DESIGN.md` item 6 (deliverable **D4**).  This directory is the port of
the honest §10 gate chain

`GateInput → toGateKernelFS → toQ3KernelFS → honestGateFS_of_rows →
exists_honestGateFS_of_fsRows → …_of_regime_rows → …_of_honestInterface`

from the corpus's `Q3KernelFS` to the **`All`** vocabulary
`Work.BoseBoxFock.Q3KernelFSAll` of the frozen module
`Submission/Work/BoseBoxFock/AllDefs.lean`, whose single difference from
`Q3KernelFS` is its `q2exLowerR` field:

* it is stated against the corrected first-quantised object `F.Q2exAll`
  (`= Σ_k ρ(Ŵ₁ω(k) + Ŵ₁ω(0)) n_k`, **all** labels including `k = 0`), not
  `F.Q2ex` (which drops the label `0`), and
* it is restricted to the `𝓜`-window `T.NWindow E.bigM Ψ` (its only consumer,
  `thm:Control3Q`'s assembly, applies it at a window state).

The point of the port is that the corrected row `Work.BoseRowQ2.RowQ2AllRegimeN`
carries *exactly* the content of the new `q2exLowerR` field: it is
`2ρŴ₁ω(0)⟨Gop⟩ ≤ ⟨Q2exAll⟩ + (b/400)⟨gapOpT⟩`, and the field adds only the
**reserve** `½⟨dNumOpR (RHi ∧ ¬P_H^q)⟩`, which is free
(`Work.BoseGateFS.Reserve.qw_dNumOpR_nonneg`).  The old chain, in contrast,
consumed the *reserved* row at `Q2ex`, i.e. `⟨Q2ex⟩ + (b/400)⟨gapOpT⟩ +
½⟨dNumOpR⟩`; feeding it from `RowQ2AllRegimeN` would need the extra obligation
`RowReserveLabelZero : 2ρŴ₁ω(0)⟨n₀⟩ ≤ ½⟨dNumOpR (rHi ∖ P_H^q)⟩`, which is
numerically hopeless (`Submission/Work/BoseRowQ2/GateAll.lean`, retired by the
lead).  Here there is **no** `RowReserveLabelZero` anywhere: the label-`0`
content of the row is what `Q2exAll` already pays for.

## What is in this file

* `GateInputAll` — the honest §10 bundle `GateInput` with the corrected row; its
  `q2exLowerR` field is **reserve-free** (exactly `RowQ2AllRegimeN`'s content,
  plus the window), the reserve being added once and for all in
  `GateInputAll.toQ3KernelFSAll`;
* `HonestRowsAll` — the row bundle `HonestRows` with the corrected row;
* `HonestInterfaceL` — the decay-free interface of `BOSE_ALL_DESIGN.md` item 7,
  transcribed field for field from the type-checked statement in
  `Submission/Work/BOSE_ALL_STATEMENTS.lean.txt`.

Everything else is derived in the sibling modules.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR
open Work.BoseBoxFock
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- **The honest §10 bundle, `All` vocabulary.**

Same fields as `Work.BoseGateFS.GateInput`, except that the `Q₂^ex` row is
stated against the corrected `F.Q2exAll` (all labels) and is **reserve-free**:

`2ρŴ₁ω(0)⟨Ψ, G Ψ⟩ ≤ ⟨Ψ, Q₂^{ex,all}(Kz z) Ψ⟩ + (b/400)⟨Ψ, gapOp Ψ⟩`

for every state in the `𝓜`-window.  This is exactly FS `eq:Q3Cancels` in the
form in which the corpus's row 3 is *provably* true (`RowQ2AllRegimeN`); the
reserve `½⟨dNumOpR (RHi ∖ P_H^q)⟩` of the frozen `Q3KernelFSAll.q2exLowerR` is
supplied downstream by nonnegativity, so no extra hypothesis is needed here. -/
structure GateInputAll (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) where
  /-- the smoothed kinetic symbol, as a function of the momentum. -/
  tauF : EuclideanSpace ℝ (Fin 3) → ℝ
  tau_eq : ∀ k : Mode, E.tau k = tauF (F.kmom k)
  tau_nonneg : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ tauF p
  tau_even : ∀ p : EuclideanSpace ℝ (Fin 3), tauF (-p) = tauF p
  /-- `Ŵ₁ ≥ 0` below the `P_H^q` threshold (FS §11). -/
  W1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k
  heT0 : 0 ≤ E.eT
  heT1 : E.eT ≤ 1
  /-- `‖k‖²/2 ≤ 𝒜_k` on `P_H^q`, density-uniform in `ρ`. -/
  A_ge : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    ‖F.kmom q‖ ^ 2 / 2 ≤ (KzEnvAt E ρ).A q
  /-- FS `eq:BoverA` on `P_H^q`, density-uniform in `ρ`. -/
  ABq : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    2 * |(KzEnvAt E ρ).B q| ≤ (KzEnvAt E ρ).A q
  /-- **K3** at the honest (smoothed) data, density-uniform in `ρ`. -/
  alpha_lip : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode,
    F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
      ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  /-- **K5** at the honest data, density-uniform in `ρ`. -/
  intOne : ∀ ρ : ℝ, AdmRho E ρ →
    |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
      ≤ K₀ * ρ * E.aScat * E.KH⁻¹
  /-- **FS `eq:Q3Cancels` with `Q₂^{ex,all}`** (reserve-free, window-restricted). -/
  q2exLowerR : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
    2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2exAll (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
  /-- **the box-model equation**: the commutator kernel of `F` is the χ-kernel of
  the momentum *difference*. -/
  boxKernel : ∀ i j : Mode, F.ccrK i j
    = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
      - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
        * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j)
  /-- the corrected τ-free bundle (the potential/χ/label rows). -/
  kink : KinkFS K₀ F T E

/-! ## 2. The honest row bundle, `All` form -/

/-- **The honest §11/§12 rows of the `All` gate**: `HonestRows` with `hq2`
replaced by the corrected, reserve-free, windowed `Q₂^{ex,all}` row. -/
structure HonestRowsAll (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) where
  hv : FSParamsView E
  kink : KinkFS K₀ F T E
  hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q
  hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k
  hbox : ∀ i j : Mode, F.ccrK i j
    = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
      - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
        * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j)
  hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
      ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  hint : ∀ ρ : ℝ, AdmRho E ρ →
    |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
      ≤ K₀ * ρ * E.aScat * E.KH⁻¹
  /-- the corrected row (reserve-free, window-restricted) -/
  hq2 : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
    2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2exAll (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
  hatChi_small : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  sum_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  form_upper : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s))
      ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat

/-! ## 3. The decay-free interface `HonestInterfaceL`

`BOSE_ALL_DESIGN.md` item 7 / `BOSE_ALL_STATEMENTS.lean.txt` lines 309–345: the
same rows as `Work.BoseRowsFS.HonestInterface`, with the two *pointwise decay*
rows on `ĝ₀` and `Ŵ₁` (which are **false** for `v = |x|^{−3/2}·1_B`) replaced by
a sup bound, a Lipschitz bound, a cube choice `Ng' ≥ Ng` and a UV tail bound over
the **full** dual lattice (finite-subset form, so that no `tsum` junk enters).

This is a verbatim transcription of the design's field list, kept so that the
design's `HonestInterfaceL` exists in the workspace; it is **superseded** as the
working interface by

    `Work.BoseRowsL.HonestInterfaceL`  (`Submission/Work/BoseRowsL/Defs.lean`),

which is the same field list plus one field `tailC` — the *continuum* far tail
`(2π)⁻³∫_{‖p‖>2Λ}(Ŵ₁² + ĝ²)/(4p²) ≤ Cw²a(R/ℓ)⁴`.  `tailC` is needed because
`tailL` controls only the *lattice* tail, and passing from it to the continuum
tail costs `Σ_far h³(CaRh)²/‖k‖² = ∞`.  Both gates are provided by this
directory:

* `exists_honestGateFSAll_of_honestInterfaceL` — for the live, inhabited
  `Work.BoseRowsL.HonestInterfaceL`;
* `exists_honestGateFSAll_of_designInterfaceL` — for the structure below.

**Warning (for the interface's designers).**  The `tailL` field below bounds the
lattice tail of the **uncut** `chat (W1fun v h (ellH v μ))`; the hypotheses of the
design's problem (`0 < a v`, `v ≥ 0`, radial, compact support) do not license that
decay (the decay of `Ŵ₁` is governed by the smoothness of `v`,
`BoseB7AK/FINDING_W1rows.md` §3, and the review of `BoseGateAll/exists_honestInterfaceL`
recorded the same objection), whereas the honest model's `Ŵ₁` is the *UV-cut* one,
which vanishes on the tail by construction.  Hence `tailL` alone is not enough and
the `BoseRowsL` interface adds `tailC`.  Nothing in this directory depends on
`tailL` being inhabited.
-/
structure HonestInterfaceL {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (R : ℝ) (hthr : Work.BoseGateFS.GateThresholds v h fc fu R) where
  Cw : ℝ
  Cw_nonneg : 0 ≤ Cw
  bndW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p : ℝ³,
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ Cw * _root_.BoseGases.a v
  lipW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p q : ℝ³,
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
      - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q| ≤ Cw * _root_.BoseGases.a v * R * ‖p - q‖
  Ng' : ℝ → ℕ
  Ng'_ge : ∀ μ, hthr.Ng μ ≤ Ng' μ
  cutR : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    1 / R ≤ 2 * uvRad (ellH v μ) (Ng' μ)
  tailL : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, Ng' μ ≤ N →
    ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, uvRad (ellH v μ) N < ‖(ellH v μ)⁻¹ • Work.BoseB4.vec n‖) →
      ellH v μ ^ (-(3 : ℝ)) * ∑ n ∈ S,
          (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) ((ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
                ((ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
          / ‖(ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
        ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ellH v μ) ^ 4
  fsp : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ)
  fspKz : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
    Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
  rkh : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹
  a16 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (Work.BoseRowsFS.honE v h fc fu HM μ).aScat * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      / ((Work.BoseRowsFS.honE v h fc fu HM μ).s * (Work.BoseRowsFS.honE v h fc fu HM μ).ell)
      ≤ 1 / 16

end Work.BoseGateAll

end
