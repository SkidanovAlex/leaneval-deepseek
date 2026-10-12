import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Fourier.T0Form_slot_eq_dirichlet
import Submission.Work.SmallBoxBridge.Fourier.peel_slot_abox
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The spectral-cutoff box-kinetic word (`𝒯_B`) — definitions

FS `final_v2.tex` `eq:HBU`/`eq:appTB`:

    𝒯_B = ½·ε_T·(1+π⁻²)⁻¹·(dℓ)⁻²·Q_B + Q_B·χ_B·[√−Δ − (dsℓ)⁻¹]₊²·χ_B·Q_B .

This module names the corpus object: a *box-localised, `Q_B`-projected,
spectrally-cutoff* kinetic word, with the box realised as an arbitrary
measurable set `A` (the sliding `B(u) = dlBox ℓ d u` in the applications),
its window `χ` (the sliding `χ_B = chiB ℓ d u`), its volume `volA` and the
ambient many-particle box `abox N a`.

## The one-body core

* `boxP volA A i Φ` — the mean of `Φ` over `A` in slot `i` (`P_{B,i}Φ`);
* `boxQ volA A i Φ = Φ − boxP …` — the mean-free projection (`Q_{B,i}Φ`);
* `tBamp χ p Ψ i x = ∫_z χ(z)e^{−i⟪p,z⟫}·Ψ(x_{i←z})dz` — the windowed
  exponential amplitude (the `Q_Bχ_Be^{−ip·}`-slot of FS's `b_p^†`);
* `tBdiagForm a A volA χ F Ψ` — the `p`-space diagonal form
  `Σ_i (2π)⁻³∫_p F(‖p‖)·∫_{abox N a}‖tBamp χ p (Q_{B,i}Ψ) i x‖² dx`;
* `tBwordKin a A volA χ c Ψ = tBdiagForm a A volA χ (fsKinCoeff c) Ψ` —
  the spectral half `Σ_i Q_{B,i}χ_B[√−Δ−c]₊²χ_BQ_{B,i}` of `𝒯_B`
  (`fsKinCoeff c r = [r−c]₊²`, `SmallBoxBogolubovKinetic`);
* `cnPlusBox a A volA Ψ` — the box excited count `Σ_i‖Q_{B,i}Ψ‖²_{L²(abox N a)}`;
* `tBword a A volA χ s ε c Ψ` — **`𝒯_B`**: the gap part
  `½ε(1+π⁻²)⁻¹s⁻²·cnPlusBox` plus `tBwordKin`;
* `winErrBox a A volA χ Ψ` — the window-derivative error
  `Σ_i∫_{abox}(Σ_k(∂_kχ)²)(x_i)·(Q_{B,i}Ψ)²`.

## Conventions

* `p`-Fourier is the Bridge's `p`-convention (`kinFT`), and `F(‖p‖)` is the
  radial symbol; for `F = ‖·‖²` the symbol of `−Δ`.
* the window `χ` is a *free* parameter (no geometry is built into the
  definition): the two structural theorems of this chapter are stated for
  `ContDiff ℝ ∞ χ`, `HasCompactSupport χ`, `tsupport χ ⊆ acube a` and a sup
  bound `|χ x| ≤ Cχ`, so that the sliding `χ_B = chiB ℓ d u` (whose
  `tsupport ⊆ dlBox ℓ d u ⊆ acube ℓ`) instantiates both.
* `boxQ` needs only that the slot-`i` mean be slot-independent, which holds
  for *any* `A` — this is why the `Q_B`-projection is free for the slot-`i`
  derivative (`fderiv_boxQ_kcDir`).

## What this chapter proves about `tBword` (see `NOTES.md`)

(a) **gap absorption** (`Gap.lean`): `tbGapPart s ε·cnPlusBox ≤ tBword`
    unconditionally, and, in the FS regime `s·C′√(μ(av)) ≤ √ε_T`, the whole
    excited penalty is absorbed: `C′²μ(av)·cnPlusBox ≤ tBword`
    (FS `eq:appgapestimate`, the Session-226 `eT_gap_absorbs_onebody`
    template);
(b) **spectral domination** (`Domination.lean`): the symbol inequality
    `[√−Δ−c]₊² ≤ −Δ` gives
    `tBwordKin ≤ 2Cχ²·kinWord N a Ψ + 2·winErrBox`
    (the Bridge's `T0Form_le_kinWord` form at the general per-box geometry),
    and the *sharp indicator* companion
    `tBdiagForm a A volA 1_A (‖·‖²) Ψ = kinWord N a Ψ`
    — the exact no-substitute identity of `SmallBoxSliding/NOTES.md` §7(e):
    with a plain box window the sliding sum has no room for the gap, so the
    spectral cutoff and the `Q_B`-projection are essential.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-! ## 1  The box mean-free projection `Q_B` -/

/-- **`P_{B,i}`** — the mean of `Φ` over the set `A` in slot `i` (the box
condensate projection; `volA` is `|A|`). -/
noncomputable def boxP (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : X N → ℝ) (x : X N) : ℝ :=
  (1 / volA) * ∫ z in A, Φ (Function.update x i z)

/-- **`Q_{B,i}`** — the mean-free projection over `A` in slot `i`. -/
noncomputable def boxQ (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : X N → ℝ) : X N → ℝ :=
  fun x => Φ x - boxP volA A i Φ x

/-- The box excited count `n₊(B) = Σ_i‖Q_{B,i}Ψ‖²` over the ambient box. -/
noncomputable def cnPlusBox (a : ℝ) (A : Set ℝ³) (volA : ℝ) {N : ℕ}
    (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N a, (boxQ volA A i Ψ x) ^ 2

/-! ## 2  The windowed-exponential amplitude and the `p`-diagonal form -/

/-- The windowed `p`-mode amplitude of the slot-`i` fibre,
`∫_z χ(z)e^{−i⟪p,z⟫}Ψ(x_{i←z})dz` (the `χ_Be^{−ip·}`-slot of FS's
`b_p^†`; the amplitude does not depend on `x i`). -/
noncomputable def tBamp (χ : ℝ³ → ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ)
    (i : Fin N) (x : X N) : ℂ :=
  ∫ z : ℝ³, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
    (Ψ (Function.update x i z) : ℂ)

/-- The `p`-space diagonal kinetic form of a symbol `F`,

    `Σ_i (2π)⁻³∫_p F(‖p‖)·(a³)⁻¹·∫_{abox N a}‖tBamp χ p (Q_{B,i}Ψ) i x‖²dx`.

The `(a³)⁻¹ = |acube a|⁻¹` is the *slot-volume* normalisation which makes this
the quadratic form of the one-body operator `Σ_i Q_{B,i}χ_iF(√−Δ_i)χ_iQ_{B,i}`
on `L²(abox N a)` (the amplitude is constant in the slot-`i` coordinate, so the
ambient integral over-counts that slot by `a³`); it is exactly the Bridge's
`T0Form` normalisation `(s³)⁻¹`. -/
noncomputable def tBdiagForm (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ * ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2)

/-- **The spectral half of `𝒯_B`**:
`Σ_i Q_{B,i}χ_B[√−Δ−(dsℓ)⁻¹]₊²χ_BQ_{B,i}`, written in the windowed
exponential Fourier form with the symbol `fsKinCoeff c = [·−c]₊²`. -/
noncomputable def tBwordKin (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (c : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  tBdiagForm a A volA χ (fsKinCoeff c) Ψ

/-- The window-derivative error of the box word,
`Σ_i∫_{abox}|∇χ(x_i)|²·(Q_{B,i}Ψ)²` (the Bridge's `winErrorQ` at the
per-box geometry). -/
noncomputable def winErrBox (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N a,
    (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2) *
      (boxQ volA A i Ψ x) ^ 2

/-! ## 3  The `𝒯_B` word -/

/-- The FS bookkeeping factor `(1+π⁻²)⁻¹` of `eq:appTB`. -/
noncomputable def tbPiFactor : ℝ := (1 + (Real.pi ^ 2)⁻¹)⁻¹

/-- The gap coefficient `½ε_T(1+π⁻²)⁻¹s⁻²` of `eq:appTB`
(`s` is the box side, `s = dℓ` in the sliding application). -/
noncomputable def tbGapCoeff (s ε : ℝ) : ℝ :=
  (1 / 2) * ε * tbPiFactor * (s ^ 2)⁻¹

/-- **`𝒯_B`** — FS `eq:appTB`: the renormalised small-box kinetic word
`½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B + Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊²χ_BQ_B`. -/
noncomputable def tBword (a : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (s ε c : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  tbGapCoeff s ε * cnPlusBox a A volA Ψ + tBwordKin a A volA χ c Ψ

/-! ## 4  The sliding instantiation (`A = B(u)`, `χ = χ_B`, `a = ℓ`, `s = dℓ`) -/

/-- **The per-`u`-box `𝒯_B` word of the sliding chapter**: the box is FS's
`B(u) = dlBox ℓ d u`, the window is the smooth corpus cutoff
`χ_B = chiB ℓ d u = χ(x/ℓ)χ(x/(dℓ)−u)`, the box volume is `boxMass ℓ d u`,
the ambient box is the big box `abox N ℓ` and the box side is `dℓ`. -/
noncomputable def tBwordB (N : ℕ) (ℓ d ε c : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  tBword ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) (chiB ℓ d u) (ℓ * d) ε c Φ

/-- The box excited count of the sliding box `B(u)`. -/
noncomputable def cnPlusBoxB (N : ℕ) (ℓ d : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  cnPlusBox ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ

/-- The per-`u` spectral half of `𝒯_B`. -/
noncomputable def tBwordKinB (N : ℕ) (ℓ d : ℝ) (c : ℝ) (u : ℝ³)
    (Φ : X N → ℝ) : ℝ :=
  tBwordKin ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) (chiB ℓ d u) c Φ

end Work.SmallBoxTBWord
